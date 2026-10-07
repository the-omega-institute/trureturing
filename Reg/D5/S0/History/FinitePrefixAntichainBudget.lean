import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration
import D5.S0.History.FinitePrefixAntichainBudget
import Reg.Support.DependentFamily
import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.BigOperators.Pi
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.History.FinitePrefixAntichainBudget
namespace Reg.D5.S0.History.FinitePrefixAntichainBudget
universe u v
noncomputable section
open Classical
abbrev signature : Signature where
  Params := Σ E : Type u, Σ V : Type v, List E → V
  State := fun p => List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} := realize signature
  (fun _ p h => p.2.2 h) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {E : Type u} {V : Type v} [DecidableEq E] [AddCommMonoid V]
    [Preorder V] [IsOrderedAddMonoid V] (m : List E → V),
    (∀ h (C : Finset E), ∑ a ∈ C, m (h ++ [a]) ≤ m h) →
    ∀ K : Finset (List E),
    (∀ h ∈ K, ∀ k ∈ K, h.IsPrefix k → h = k) →
    ∑ h ∈ K, m h ≤ R.readout () ⟨E, V, m⟩ []

def rejected : Realization signature.{u,v} := realize signature
  (fun _ p _ => p.2.2 (if h : Nonempty p.1 then [Classical.choice h] else []))
  (fun e => nomatch e)

def sample : List (ULift.{u} Unit) → (ULift.{v} Unit → ℕ) :=
  fun h _ => if h = [] then 1 else 0

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro h
  have localBudget : ∀ xs (C : Finset (ULift.{u} Unit)),
      ∑ a ∈ C, sample (xs ++ [a]) ≤ sample xs := by
    intro xs C
    intro z
    simp [sample, Finset.sum_apply]
  have bound := h sample localBudget {[]} (by simp)
  have b := bound (ULift.up ())
  simpa [rejected, realize, sample, Finset.sum_apply] using b

def registration : Registration arena.{u,v} (arena.Law actual) where
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
  dependence := by
    intro i
    exact ⟨⟨ULift.{u} Unit, (ULift.{v} Unit → ℕ), sample⟩, [], [⟨()⟩], by
      intro he
      have := congrFun he (ULift.up ())
      simpa [actual, realize, sample] using this⟩

def selection : _root_.Reg.Support.SourceSelection := {
  owner := `D5.S0.History.FinitePrefixAntichainBudget
  coordinates := #[0, 1, 6]
  readouts := #[{path := #["body", "body", "body", "body", "body", "body",
    "body", "body", "body", "body", "arg"], stateOperand := some #["arg"]}] }

noncomputable def registration_1.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S0.History.FinitePrefixAntichainBudget.result.{u_1, u_2}) (type_of% (realize.{max (u_1 + 1) (u_2 + 1), u_1, 0, u_2, 0} signature.{u_1, u_2} (fun _ p h => p.2.2 h) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S0") "History") "FinitePrefixAntichainBudget") "result") "Reg.D5.S0.History.FinitePrefixAntichainBudget/Reg.D5.S0.History.FinitePrefixAntichainBudget.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (u_1 + 1) (u_2 + 1), u_1, 0, u_2, 0} signature.{u_1, u_2} (fun _ p h => p.2.2 h) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S0.History.FinitePrefixAntichainBudget, definition := none, coordinates := #[0, 1, 6], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S0.History.FinitePrefixAntichainBudget, declaration := `D5.S0.History.FinitePrefixAntichainBudget.result, part := .type, path := [], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S0.History.FinitePrefixAntichainBudget, declaration := `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S0.History.FinitePrefixAntichainBudget, declaration := `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S0.History.FinitePrefixAntichainBudget, declaration := `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S0.History.FinitePrefixAntichainBudget, declaration := `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2] }], facts := [`Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.canonicalArenaFact, `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.canonicalObjectArenaFact, `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.sourceBridgeFact, `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.observationFact0, `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.anchorEnumeration }


#print axioms registration
end
end Reg.D5.S0.History.FinitePrefixAntichainBudget


noncomputable def Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.canonicalArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_2 + 1), u_1, 0, u_2, 0} :=
  Reg.D5.S0.History.FinitePrefixAntichainBudget.arena.{u_1, u_2}
noncomputable def Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.canonicalArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"History\",\"FinitePrefixAntichainBudget\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"History\",\"FinitePrefixAntichainBudget\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S0.History.FinitePrefixAntichainBudget, declaration := `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S0.History.FinitePrefixAntichainBudget, declaration := `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence
noncomputable def Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.canonicalObjectArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_2 + 1), u_1, 0, u_2, 0} :=
  Reg.D5.S0.History.FinitePrefixAntichainBudget.arena.{u_1, u_2}
noncomputable def Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.canonicalObjectArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"History\",\"FinitePrefixAntichainBudget\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"History\",\"FinitePrefixAntichainBudget\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S0.History.FinitePrefixAntichainBudget, declaration := `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S0.History.FinitePrefixAntichainBudget, declaration := `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence


noncomputable def Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.sourceLaw.{u_1, u_2} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u_1 + 1) (u_2 + 1), u_1, 0, u_2, 0} (Reg.D5.S0.History.FinitePrefixAntichainBudget.arena.) (Reg.D5.S0.History.FinitePrefixAntichainBudget.registration.{u_1, u_2}).actual

noncomputable def Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.sourceBridgeFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S0\",\"History\",\"FinitePrefixAntichainBudget\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"History\",\"FinitePrefixAntichainBudget\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S0.History.FinitePrefixAntichainBudget, declaration := `D5.S0.History.FinitePrefixAntichainBudget.result, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S0.History.FinitePrefixAntichainBudget, declaration := `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (Reg.D5.S0.History.FinitePrefixAntichainBudget.registration.{u_1, u_2}).bridge

noncomputable def Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.observation0.{u_1, u_2} : {E : Type u_1} →
  {V : Type u_2} →
    [DecidableEq.{u_1 + 1} E] →
      [inst : AddCommMonoid.{u_2} V] →
        [inst_1 : Preorder.{u_2} V] →
          [@IsOrderedAddMonoid.{u_2} V inst inst_1] →
            (m : List.{u_1} E → V) →
              (localBudget :
                  ∀ (h : List.{u_1} E) (C : Finset.{u_1} E),
                    @LE.le.{u_2} V (@Preorder.toLE.{u_2} V inst_1)
                      (@Finset.sum.{u_1, u_2} E V inst C fun (a : E) =>
                        m
                          (@HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} E) (List.{u_1} E) (List.{u_1} E)
                            (@instHAppendOfAppend.{u_1} (List.{u_1} E) (@List.instAppend.{u_1} E)) h
                            (@List.cons.{u_1} E a (@List.nil.{u_1} E))))
                      (m h)) →
                (K : Finset.{u_1} (List.{u_1} E)) →
                  (antichain :
                      ∀ (h : List.{u_1} E),
                        @Membership.mem.{u_1, u_1} (List.{u_1} E) (Finset.{u_1} (List.{u_1} E))
                            (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (List.{u_1} E)) (List.{u_1} E)
                              (@Finset.instSetLike.{u_1} (List.{u_1} E)))
                            K h →
                          ∀ (k : List.{u_1} E),
                            @Membership.mem.{u_1, u_1} (List.{u_1} E) (Finset.{u_1} (List.{u_1} E))
                                (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (List.{u_1} E)) (List.{u_1} E)
                                  (@Finset.instSetLike.{u_1} (List.{u_1} E)))
                                K k →
                              @List.IsPrefix.{u_1} E h k → @Eq.{u_1 + 1} (List.{u_1} E) h k) →
                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{max (u_1 + 1) (u_2 + 1),
                        u_1, 0, u_2, 0}
                      Reg.D5.S0.History.FinitePrefixAntichainBudget.signature.{u_1, u_2} PUnit.unit.{1}
                      (@Sigma.mk.{u_1 + 1, max (max u_1 u_2) (u_2 + 1)} (Type u_1)
                        (fun (E : Type u_1) =>
                          @Sigma.{u_2 + 1, max u_1 u_2} (Type u_2) fun (V : Type u_2) => List.{u_1} E → V)
                        E (@Sigma.mk.{u_2 + 1, max u_1 u_2} (Type u_2) (fun (V : Type u_2) => List.{u_1} E → V) V m)) :=
  fun {E : Type u_1} {V : Type u_2} [DecidableEq.{u_1 + 1} E] [AddCommMonoid.{u_2} V] [Preorder.{u_2} V]
    [@IsOrderedAddMonoid.{u_2} V inst_1 inst_2] (m : List.{u_1} E → V)
    (localBudget :
      ∀ (h : List.{u_1} E) (C : Finset.{u_1} E),
        @LE.le.{u_2} V (@Preorder.toLE.{u_2} V inst_2)
          (@Finset.sum.{u_1, u_2} E V inst_1 C fun (a : E) =>
            m
              (@HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} E) (List.{u_1} E) (List.{u_1} E)
                (@instHAppendOfAppend.{u_1} (List.{u_1} E) (@List.instAppend.{u_1} E)) h
                (@List.cons.{u_1} E a (@List.nil.{u_1} E))))
          (m h))
    (K : Finset.{u_1} (List.{u_1} E))
    (antichain :
      ∀ (h : List.{u_1} E),
        @Membership.mem.{u_1, u_1} (List.{u_1} E) (Finset.{u_1} (List.{u_1} E))
            (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (List.{u_1} E)) (List.{u_1} E)
              (@Finset.instSetLike.{u_1} (List.{u_1} E)))
            K h →
          ∀ (k : List.{u_1} E),
            @Membership.mem.{u_1, u_1} (List.{u_1} E) (Finset.{u_1} (List.{u_1} E))
                (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (List.{u_1} E)) (List.{u_1} E)
                  (@Finset.instSetLike.{u_1} (List.{u_1} E)))
                K k →
              @List.IsPrefix.{u_1} E h k → @Eq.{u_1 + 1} (List.{u_1} E) h k) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{max (u_1 + 1) (u_2 + 1), u_1, 0, u_2, 0}
    Reg.D5.S0.History.FinitePrefixAntichainBudget.signature.{u_1, u_2}
    Reg.D5.S0.History.FinitePrefixAntichainBudget.actual.{u_1, u_2} PUnit.unit.{1}
    (@Sigma.mk.{u_1 + 1, max (max u_1 u_2) (u_2 + 1)} (Type u_1)
      (fun (E : Type u_1) => @Sigma.{u_2 + 1, max u_1 u_2} (Type u_2) fun (V : Type u_2) => List.{u_1} E → V) E
      (@Sigma.mk.{u_2 + 1, max u_1 u_2} (Type u_2) (fun (V : Type u_2) => List.{u_1} E → V) V m))
    (@List.nil.{u_1} E)

noncomputable def Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.observationFact0.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S0\",\"History\",\"FinitePrefixAntichainBudget\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"History\",\"FinitePrefixAntichainBudget\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S0.History.FinitePrefixAntichainBudget, declaration := `D5.S0.History.FinitePrefixAntichainBudget.result, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S0.History.FinitePrefixAntichainBudget, declaration := `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.varyingLawInput.{u_1, u_2} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.canonicalArenaOperand.{u_1, u_2})
noncomputable def Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.varyingLaw.{u_1, u_2}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"History\",\"FinitePrefixAntichainBudget\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"

noncomputable def Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.statementExclusion.{u_1, u_2} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"History\",\"FinitePrefixAntichainBudget\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S0\",\"History\",\"FinitePrefixAntichainBudget\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S0.History.FinitePrefixAntichainBudget, declaration := `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  statementLocation := { owner := `D5.S0.History.FinitePrefixAntichainBudget, declaration := `D5.S0.History.FinitePrefixAntichainBudget.result, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S0.History.FinitePrefixAntichainBudget.registration.{u_1, u_2}).actual (Reg.D5.S0.History.FinitePrefixAntichainBudget.registration.{u_1, u_2}).variation.2.choose (Reg.D5.S0.History.FinitePrefixAntichainBudget.registration.{u_1, u_2}).variation.1 (Reg.D5.S0.History.FinitePrefixAntichainBudget.registration.{u_1, u_2}).variation.2.choose_spec

noncomputable def Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1.descriptorFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"History\",\"FinitePrefixAntichainBudget\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"History\",\"FinitePrefixAntichainBudget\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S0.History.FinitePrefixAntichainBudget, declaration := `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S0.History.FinitePrefixAntichainBudget, declaration := `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))
