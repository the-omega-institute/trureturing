import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration
import D5.S0.History.WellFoundedLeafMassConservation
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.History.WellFoundedLeafMassConservation
namespace Reg.D5.S0.History.WellFoundedLeafMassConservation
universe u
noncomputable section
open Classical

abbrev signature : Signature where
  Params := Σ E : Type u, Σ _T : Set (List E), List E → ENNReal
  State := fun p => List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ENNReal
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p h => p.2.2 h) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [Countable E] (T : Set (List E))
    (_root : [] ∈ T)
    (_prefixclosed : ∀ ⦃h k : List E⦄, h.IsPrefix k → k ∈ T → h ∈ T)
    (m : List E → ENNReal)
    (_wf : WellFounded (fun k h : List E =>
      k ∈ T ∧ h ∈ T ∧ ∃ a : E, k = h ++ [a]))
    (_localMass : ∀ h ∈ T, ¬ (h ∈ T ∧ ∀ a : E, h ++ [a] ∉ T) →
      m h = ∑' a : E, if h ++ [a] ∈ T then m (h ++ [a]) else 0),
    (∑' l : {h : List E // h ∈ T ∧ ∀ a : E, h ++ [a] ∉ T}, m l.val) =
      R.readout () ⟨E, T, m⟩ []

def rejected : Realization signature.{u} := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

def sample : List (ULift.{u} Unit) → ENNReal := fun h => if h = [] then 1 else 0

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let T : Set (List (ULift.{u} Unit)) := {[]}
  have root : [] ∈ T := by simp [T]
  have pc : ∀ ⦃h k : List (ULift.{u} Unit)⦄, h.IsPrefix k → k ∈ T → h ∈ T := by
    intro h k hp hk
    have hk' : k = [] := hk
    subst k
    simpa [T] using hp
  have wf : WellFounded (fun k h : List (ULift.{u} Unit) =>
      k ∈ T ∧ h ∈ T ∧ ∃ a, k = h ++ [a]) := by
    constructor
    intro h
    constructor
    intro k hk
    rcases hk with ⟨hk, _, a, ha⟩
    have hk' : k = [] := hk
    subst k
    simp at ha
  have terminal : ∀ h ∈ T, h ∈ T ∧ ∀ a : ULift.{u} Unit, h ++ [a] ∉ T := by
    intro h ht
    exact ⟨ht, by intro a; simp [T]⟩
  have bad := h T root pc sample wf (by
    intro h ht hn
    exact (hn (terminal h ht)).elim)
  have good := result T root pc sample wf (by
    intro h ht hn
    exact (hn (terminal h ht)).elim)
  rw [good] at bad
  simpa [sample, rejected, realize] using bad

def registration : Registration arena.{u} (arena.Law actual) where
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
    exact ⟨⟨ULift.{u} Unit, {[]}, sample⟩, [], [⟨()⟩], by
      simp [actual, realize, sample]⟩

def selection : _root_.Reg.Support.SourceSelection := {
  owner := `D5.S0.History.WellFoundedLeafMassConservation
  coordinates := #[0, 2, 5]
  readouts := #[{path := #["body", "body", "body", "body", "body", "body",
    "body", "body", "arg"], stateOperand := some #["arg"]}] }

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S0.History.WellFoundedLeafMassConservation.result.{u_1}) (type_of% (realize.{u_1 + 1, u_1, 0, 0, 0} signature.{u_1} (fun _ p h => p.2.2 h) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S0") "History") "WellFoundedLeafMassConservation") "result") "Reg.D5.S0.History.WellFoundedLeafMassConservation/Reg.D5.S0.History.WellFoundedLeafMassConservation.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, 0, 0} signature.{u_1} (fun _ p h => p.2.2 h) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S0.History.WellFoundedLeafMassConservation, definition := none, coordinates := #[0, 2, 5], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S0.History.WellFoundedLeafMassConservation, declaration := `D5.S0.History.WellFoundedLeafMassConservation.result, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S0.History.WellFoundedLeafMassConservation, declaration := `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S0.History.WellFoundedLeafMassConservation, declaration := `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S0.History.WellFoundedLeafMassConservation, declaration := `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S0.History.WellFoundedLeafMassConservation, declaration := `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.canonicalArenaFact, `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.canonicalObjectArenaFact, `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.sourceBridgeFact, `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.observationFact0, `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.anchorEnumeration }


#print axioms registration
end
end Reg.D5.S0.History.WellFoundedLeafMassConservation


noncomputable def Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, 0, 0} :=
  Reg.D5.S0.History.WellFoundedLeafMassConservation.arena.{u_1}
noncomputable def Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"History\",\"WellFoundedLeafMassConservation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"History\",\"WellFoundedLeafMassConservation\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S0.History.WellFoundedLeafMassConservation, declaration := `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S0.History.WellFoundedLeafMassConservation, declaration := `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, 0, 0} :=
  Reg.D5.S0.History.WellFoundedLeafMassConservation.arena.{u_1}
noncomputable def Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"History\",\"WellFoundedLeafMassConservation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"History\",\"WellFoundedLeafMassConservation\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S0.History.WellFoundedLeafMassConservation, declaration := `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S0.History.WellFoundedLeafMassConservation, declaration := `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, 0, 0}
  Reg.D5.S0.History.WellFoundedLeafMassConservation.arena.{u_1}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{u_1 + 1, u_1, 0, 0, 0}
    Reg.D5.S0.History.WellFoundedLeafMassConservation.arena.{u_1}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, 0, 0}
      Reg.D5.S0.History.WellFoundedLeafMassConservation.arena.{u_1}
      Reg.D5.S0.History.WellFoundedLeafMassConservation.actual.{u_1})
    Reg.D5.S0.History.WellFoundedLeafMassConservation.registration.{u_1})

noncomputable def Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S0\",\"History\",\"WellFoundedLeafMassConservation\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"History\",\"WellFoundedLeafMassConservation\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S0.History.WellFoundedLeafMassConservation, declaration := `D5.S0.History.WellFoundedLeafMassConservation.result, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S0.History.WellFoundedLeafMassConservation, declaration := `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{u_1 + 1, u_1, 0, 0, 0}
  Reg.D5.S0.History.WellFoundedLeafMassConservation.arena.{u_1}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, 0, 0}
    Reg.D5.S0.History.WellFoundedLeafMassConservation.arena.{u_1}
    Reg.D5.S0.History.WellFoundedLeafMassConservation.actual.{u_1})
  Reg.D5.S0.History.WellFoundedLeafMassConservation.registration.{u_1})

noncomputable def Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.observation0.{u_1} : {E : Type u_1} →
  [Countable.{u_1 + 1} E] →
    (T : Set.{u_1} (List.{u_1} E)) →
      (root :
          @Membership.mem.{u_1, u_1} (List.{u_1} E) (Set.{u_1} (List.{u_1} E))
            (@Set.instMembership.{u_1} (List.{u_1} E)) T (@List.nil.{u_1} E)) →
        (prefixclosed :
            ∀ ⦃h k : List.{u_1} E⦄,
              @List.IsPrefix.{u_1} E h k →
                @Membership.mem.{u_1, u_1} (List.{u_1} E) (Set.{u_1} (List.{u_1} E))
                    (@Set.instMembership.{u_1} (List.{u_1} E)) T k →
                  @Membership.mem.{u_1, u_1} (List.{u_1} E) (Set.{u_1} (List.{u_1} E))
                    (@Set.instMembership.{u_1} (List.{u_1} E)) T h) →
          (m : List.{u_1} E → ENNReal) →
            (wf :
                @WellFounded.{u_1 + 1} (List.{u_1} E) fun (k h : List.{u_1} E) =>
                  And
                    (@Membership.mem.{u_1, u_1} (List.{u_1} E) (Set.{u_1} (List.{u_1} E))
                      (@Set.instMembership.{u_1} (List.{u_1} E)) T k)
                    (And
                      (@Membership.mem.{u_1, u_1} (List.{u_1} E) (Set.{u_1} (List.{u_1} E))
                        (@Set.instMembership.{u_1} (List.{u_1} E)) T h)
                      (@Exists.{u_1 + 1} E fun (a : E) =>
                        @Eq.{u_1 + 1} (List.{u_1} E) k
                          (@HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} E) (List.{u_1} E) (List.{u_1} E)
                            (@instHAppendOfAppend.{u_1} (List.{u_1} E) (@List.instAppend.{u_1} E)) h
                            (@List.cons.{u_1} E a (@List.nil.{u_1} E)))))) →
              (localMass :
                  ∀ (h : List.{u_1} E),
                    @Membership.mem.{u_1, u_1} (List.{u_1} E) (Set.{u_1} (List.{u_1} E))
                        (@Set.instMembership.{u_1} (List.{u_1} E)) T h →
                      Not
                          (And
                            (@Membership.mem.{u_1, u_1} (List.{u_1} E) (Set.{u_1} (List.{u_1} E))
                              (@Set.instMembership.{u_1} (List.{u_1} E)) T h)
                            (∀ (a : E),
                              Not
                                (@Membership.mem.{u_1, u_1} (List.{u_1} E) (Set.{u_1} (List.{u_1} E))
                                  (@Set.instMembership.{u_1} (List.{u_1} E)) T
                                  (@HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} E) (List.{u_1} E) (List.{u_1} E)
                                    (@instHAppendOfAppend.{u_1} (List.{u_1} E) (@List.instAppend.{u_1} E)) h
                                    (@List.cons.{u_1} E a (@List.nil.{u_1} E)))))) →
                        @Eq.{1} ENNReal (m h)
                          (@tsum.{0, u_1} ENNReal E ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace
                            (fun (a : E) =>
                              @ite.{1} ENNReal
                                (@Membership.mem.{u_1, u_1} (List.{u_1} E) (Set.{u_1} (List.{u_1} E))
                                  (@Set.instMembership.{u_1} (List.{u_1} E)) T
                                  (@HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} E) (List.{u_1} E) (List.{u_1} E)
                                    (@instHAppendOfAppend.{u_1} (List.{u_1} E) (@List.instAppend.{u_1} E)) h
                                    (@List.cons.{u_1} E a (@List.nil.{u_1} E))))
                                (Classical.propDecidable
                                  (@Membership.mem.{u_1, u_1} (List.{u_1} E) (Set.{u_1} (List.{u_1} E))
                                    (@Set.instMembership.{u_1} (List.{u_1} E)) T
                                    (@HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} E) (List.{u_1} E) (List.{u_1} E)
                                      (@instHAppendOfAppend.{u_1} (List.{u_1} E) (@List.instAppend.{u_1} E)) h
                                      (@List.cons.{u_1} E a (@List.nil.{u_1} E)))))
                                (m
                                  (@HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} E) (List.{u_1} E) (List.{u_1} E)
                                    (@instHAppendOfAppend.{u_1} (List.{u_1} E) (@List.instAppend.{u_1} E)) h
                                    (@List.cons.{u_1} E a (@List.nil.{u_1} E))))
                                (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                            (SummationFilter.unconditional.{u_1} E))) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_1 + 1, u_1, 0, 0, 0}
                  Reg.D5.S0.History.WellFoundedLeafMassConservation.signature.{u_1} PUnit.unit.{1}
                  (@Sigma.mk.{u_1 + 1, u_1} (Type u_1)
                    (fun (E : Type u_1) =>
                      @Sigma.{u_1, u_1} (Set.{u_1} (List.{u_1} E)) fun (_T : Set.{u_1} (List.{u_1} E)) =>
                        List.{u_1} E → ENNReal)
                    E
                    (@Sigma.mk.{u_1, u_1} (Set.{u_1} (List.{u_1} E))
                      (fun (_T : Set.{u_1} (List.{u_1} E)) => List.{u_1} E → ENNReal) T m)) :=
  fun {E : Type u_1} [Countable.{u_1 + 1} E] (T : Set.{u_1} (List.{u_1} E))
    (root :
      @Membership.mem.{u_1, u_1} (List.{u_1} E) (Set.{u_1} (List.{u_1} E)) (@Set.instMembership.{u_1} (List.{u_1} E)) T
        (@List.nil.{u_1} E))
    (prefixclosed :
      ∀ ⦃h k : List.{u_1} E⦄,
        @List.IsPrefix.{u_1} E h k →
          @Membership.mem.{u_1, u_1} (List.{u_1} E) (Set.{u_1} (List.{u_1} E))
              (@Set.instMembership.{u_1} (List.{u_1} E)) T k →
            @Membership.mem.{u_1, u_1} (List.{u_1} E) (Set.{u_1} (List.{u_1} E))
              (@Set.instMembership.{u_1} (List.{u_1} E)) T h)
    (m : List.{u_1} E → ENNReal)
    (wf :
      @WellFounded.{u_1 + 1} (List.{u_1} E) fun (k h : List.{u_1} E) =>
        And
          (@Membership.mem.{u_1, u_1} (List.{u_1} E) (Set.{u_1} (List.{u_1} E))
            (@Set.instMembership.{u_1} (List.{u_1} E)) T k)
          (And
            (@Membership.mem.{u_1, u_1} (List.{u_1} E) (Set.{u_1} (List.{u_1} E))
              (@Set.instMembership.{u_1} (List.{u_1} E)) T h)
            (@Exists.{u_1 + 1} E fun (a : E) =>
              @Eq.{u_1 + 1} (List.{u_1} E) k
                (@HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} E) (List.{u_1} E) (List.{u_1} E)
                  (@instHAppendOfAppend.{u_1} (List.{u_1} E) (@List.instAppend.{u_1} E)) h
                  (@List.cons.{u_1} E a (@List.nil.{u_1} E))))))
    (localMass :
      ∀ (h : List.{u_1} E),
        @Membership.mem.{u_1, u_1} (List.{u_1} E) (Set.{u_1} (List.{u_1} E)) (@Set.instMembership.{u_1} (List.{u_1} E))
            T h →
          Not
              (And
                (@Membership.mem.{u_1, u_1} (List.{u_1} E) (Set.{u_1} (List.{u_1} E))
                  (@Set.instMembership.{u_1} (List.{u_1} E)) T h)
                (∀ (a : E),
                  Not
                    (@Membership.mem.{u_1, u_1} (List.{u_1} E) (Set.{u_1} (List.{u_1} E))
                      (@Set.instMembership.{u_1} (List.{u_1} E)) T
                      (@HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} E) (List.{u_1} E) (List.{u_1} E)
                        (@instHAppendOfAppend.{u_1} (List.{u_1} E) (@List.instAppend.{u_1} E)) h
                        (@List.cons.{u_1} E a (@List.nil.{u_1} E)))))) →
            @Eq.{1} ENNReal (m h)
              (@tsum.{0, u_1} ENNReal E ENNReal.instAddCommMonoid ENNReal.instTopologicalSpace
                (fun (a : E) =>
                  @ite.{1} ENNReal
                    (@Membership.mem.{u_1, u_1} (List.{u_1} E) (Set.{u_1} (List.{u_1} E))
                      (@Set.instMembership.{u_1} (List.{u_1} E)) T
                      (@HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} E) (List.{u_1} E) (List.{u_1} E)
                        (@instHAppendOfAppend.{u_1} (List.{u_1} E) (@List.instAppend.{u_1} E)) h
                        (@List.cons.{u_1} E a (@List.nil.{u_1} E))))
                    (Classical.propDecidable
                      (@Membership.mem.{u_1, u_1} (List.{u_1} E) (Set.{u_1} (List.{u_1} E))
                        (@Set.instMembership.{u_1} (List.{u_1} E)) T
                        (@HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} E) (List.{u_1} E) (List.{u_1} E)
                          (@instHAppendOfAppend.{u_1} (List.{u_1} E) (@List.instAppend.{u_1} E)) h
                          (@List.cons.{u_1} E a (@List.nil.{u_1} E)))))
                    (m
                      (@HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} E) (List.{u_1} E) (List.{u_1} E)
                        (@instHAppendOfAppend.{u_1} (List.{u_1} E) (@List.instAppend.{u_1} E)) h
                        (@List.cons.{u_1} E a (@List.nil.{u_1} E))))
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                (SummationFilter.unconditional.{u_1} E))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_1 + 1, u_1, 0, 0, 0}
    Reg.D5.S0.History.WellFoundedLeafMassConservation.signature.{u_1}
    Reg.D5.S0.History.WellFoundedLeafMassConservation.actual.{u_1} PUnit.unit.{1}
    (@Sigma.mk.{u_1 + 1, u_1} (Type u_1)
      (fun (E : Type u_1) =>
        @Sigma.{u_1, u_1} (Set.{u_1} (List.{u_1} E)) fun (_T : Set.{u_1} (List.{u_1} E)) => List.{u_1} E → ENNReal)
      E
      (@Sigma.mk.{u_1, u_1} (Set.{u_1} (List.{u_1} E)) (fun (_T : Set.{u_1} (List.{u_1} E)) => List.{u_1} E → ENNReal) T
        m))
    (@List.nil.{u_1} E)

noncomputable def Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S0\",\"History\",\"WellFoundedLeafMassConservation\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"History\",\"WellFoundedLeafMassConservation\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S0.History.WellFoundedLeafMassConservation, declaration := `D5.S0.History.WellFoundedLeafMassConservation.result, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S0.History.WellFoundedLeafMassConservation, declaration := `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"History\",\"WellFoundedLeafMassConservation\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"History\",\"WellFoundedLeafMassConservation\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S0\",\"History\",\"WellFoundedLeafMassConservation\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S0.History.WellFoundedLeafMassConservation, declaration := `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S0.History.WellFoundedLeafMassConservation, declaration := `D5.S0.History.WellFoundedLeafMassConservation.result, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S0.History.WellFoundedLeafMassConservation.registration.{u_1}).actual (Reg.D5.S0.History.WellFoundedLeafMassConservation.registration.{u_1}).variation.2.choose (Reg.D5.S0.History.WellFoundedLeafMassConservation.registration.{u_1}).variation.1 (Reg.D5.S0.History.WellFoundedLeafMassConservation.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"History\",\"WellFoundedLeafMassConservation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"History\",\"WellFoundedLeafMassConservation\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S0.History.WellFoundedLeafMassConservation, declaration := `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S0.History.WellFoundedLeafMassConservation, declaration := `Reg.D5.S0.History.WellFoundedLeafMassConservation.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
