import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification
import Mathlib.Algebra.Group.ULift
import Reg.Support.DependentFamily

open _root_.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification
universe u v w z

local instance : AddGroupWithOne (ZMod 2) := (ZMod.commRing 2).toRing.toAddGroupWithOne

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => 2 ^ n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The whole source statement, with only its final power replaced by a readout. -/
def arena : Arena where
  signature := signature
  Law observation := ∀ {G : Type u} {I : Type v} {C : Type w}
    [AddCommGroup G] [Fintype I] {M : I → Type z} [Nontrivial I]
    (P : Protocol G I C M) (χ : G →+ ZMod 2)
    (D : (G × G × ((i : I) → M i)) → G)
    (hD : ∀ s : Source (I := I) χ, D (observe P s) = target s),
    (∀ a t c, Reachable P χ a t c → ∀ i x,
      ∃ s : Source (I := I) χ,
        s.1.1 = a ∧ clock s = t ∧
        P.query s.1.1 (clock s) = c ∧ s.1.2 i = x) ∧
    (∀ i, senderPeriods P χ i = ⊥ ∨ ∃ τ : G,
      τ ≠ 0 ∧ χ τ = 1 ∧ τ + τ = 0 ∧
      ∀ p, p ∈ senderPeriods P χ i ↔ p = 0 ∨ p = τ) ∧
    (∀ i j p q, p ∈ senderPeriods P χ i → q ∈ senderPeriods P χ j →
      p ≠ 0 → q ≠ 0 → p = q) ∧
    (∀ v : Source (I := I) χ, v ∈ globalPeriods P χ ↔
      v.1.1 = 0 ∧ v.2 = 0 ∧ (∀ i, v.1.2 i ∈ senderPeriods P χ i) ∧
        ∑ i, v.1.2 i = 0) ∧
    ( (activeSenders P χ).card ≤ 1 → globalPeriods P χ = ⊥) ∧
    ( (activeSenders P χ).Nonempty →
      Nonempty (globalPeriods P χ ≃+ evenSwitches (activeSenders P χ)) ∧
      Nat.card (globalPeriods P χ) = observation.readout () () ((activeSenders P χ).card - 1))

theorem actual_law : arena.{u, v, w, z}.Law actual := by
  intro G I C _ _ M _ P χ D hD
  exact period_classification P χ D hD

/-- Constant replies with an injective clock give a genuine nonempty active family. -/
theorem rejected_law : ¬ arena.{u, v, w, z}.Law rejected := by
  classical
  intro h
  let G := ULift.{u} (ZMod 2)
  let I := ULift.{v} Bool
  let C := ULift.{w} Unit
  let M : I → Type z := fun _ => ULift.{z} Unit
  let P : Protocol G I C M := {
    query := fun _ _ => ⟨()⟩
    reply := fun _ _ _ _ => ⟨()⟩ }
  let χ : G →+ ZMod 2 := AddEquiv.ulift.toAddMonoidHom
  let D : (G × G × ((i : I) → M i)) → G := fun q => q.2.1
  have hD : ∀ s : Source (I := I) χ, D (observe P s) = target s := by
    intro s
    change target s + (s.2 : G) = target s
    have hz : (s.2 : G) = 0 := by
      apply ULift.ext
      exact s.2.property
    rw [hz, add_zero]
  have hactive : (activeSenders P χ).Nonempty := by
    refine ⟨⟨false⟩, ?_⟩
    simp only [activeSenders, Finset.mem_filter, Finset.mem_univ, true_and]
    intro heq
    have hp : (⟨1⟩ : G) ∈ senderPeriods P χ ⟨false⟩ := by
      intro a t c hb x
      rfl
    rw [heq] at hp
    have hz := congrArg ULift.down (AddSubgroup.mem_bot.mp hp)
    exact one_ne_zero hz
  have hbad := ((h P χ D hD).2.2.2.2.2 hactive).2
  change Nat.card (globalPeriods P χ) = 0 at hbad
  exact (Nat.ne_of_gt (Nat.card_pos (α := globalPeriods P χ))) hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (1 : ℕ) ≠ 2
  decide

def registration : Registration arena.{u, v, w, z} (arena.Law actual) :=
  Registration.mk actual Iff.rfl
    ⟨actual_law, rejected, rejected_law⟩
    (by
      constructor
      · intro i
        refine ⟨rejected, ?_, rfl, rejected_law⟩
        intro j h
        exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
      · intro i
        exact nomatch i)
    dependence

noncomputable def registration_1.{u_1, u_2, u_3, u_4} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.period_classification.{u_1, u_2, u_3, u_4}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => 2 ^ n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ObserverMemory") "ContextUpdates") "ExactSnapshotPeriodClassification") "period_classification") "Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification/Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3, u_4})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3, u_4})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3, u_4}) ⟨(registration.{u_1, u_2, u_3, u_4})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => 2 ^ n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "body", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification, declaration := `D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.period_classification, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3, .param `u_4] },
    { owner := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification, declaration := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3, .param `u_4] },
    { owner := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification, declaration := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3, .param `u_4] },
    { owner := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification, declaration := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3, .param `u_4] },
    { owner := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification, declaration := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3, .param `u_4] }], facts := [`Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.canonicalArenaFact, `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.sourceBridgeFact, `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.observationFact0, `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification


noncomputable def Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.canonicalArenaOperand.{u_1, u_2, u_3, u_4} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena.{u_1, u_2, u_3, u_4}
noncomputable def Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.canonicalArenaFact.{u_1, u_2, u_3, u_4} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"ContextUpdates\",\"ExactSnapshotPeriodClassification\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"ContextUpdates\",\"ExactSnapshotPeriodClassification\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification, declaration := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  { owner := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification, declaration := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  .evidence
noncomputable def Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.canonicalObjectArenaOperand.{u_1, u_2, u_3, u_4} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena.{u_1, u_2, u_3, u_4}
noncomputable def Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.canonicalObjectArenaFact.{u_1, u_2, u_3, u_4} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"ContextUpdates\",\"ExactSnapshotPeriodClassification\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"ContextUpdates\",\"ExactSnapshotPeriodClassification\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification, declaration := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  { owner := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification, declaration := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  .evidence


noncomputable def Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.sourceLaw.{u_1, u_2, u_3, u_4} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena.{u_1, u_2, u_3, u_4}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena.{u_1, u_2, u_3, u_4}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena.{u_1, u_2, u_3, u_4}
      Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.actual)
    Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration.{u_1, u_2, u_3, u_4})

noncomputable def Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.sourceBridgeFact.{u_1, u_2, u_3, u_4} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"ContextUpdates\",\"ExactSnapshotPeriodClassification\",\"period_classification\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"ContextUpdates\",\"ExactSnapshotPeriodClassification\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification, declaration := `D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.period_classification, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  { owner := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification, declaration := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena.{u_1, u_2, u_3, u_4}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena.{u_1, u_2, u_3, u_4}
    Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.actual)
  Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration.{u_1, u_2, u_3, u_4})

noncomputable def Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.observation0.{u_1, u_2, u_3, u_4} : {G : Type u_1} →
  {I : Type u_2} →
    {C : Type u_3} →
      [inst : AddCommGroup.{u_1} G] →
        [inst_1 : Fintype.{u_2} I] →
          {M : I → Type u_4} →
            [Nontrivial.{u_2} I] →
              (P :
                  D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.Protocol.{u_1, u_2, u_3, u_4} G
                    I C M) →
                (χ :
                    @AddMonoidHom.{u_1, 0} G (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@AddZeroClass.toAddZero.{u_1} G
                        (@AddMonoid.toAddZeroClass.{u_1} G
                          (@SubNegMonoid.toAddMonoid.{u_1} G
                            (@AddGroup.toSubNegMonoid.{u_1} G (@AddCommGroup.toAddGroup.{u_1} G inst)))))
                      (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@AddMonoid.toAddZeroClass.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@AddMonoidWithOne.toAddMonoid.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@AddGroupWithOne.toAddMonoidWithOne.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@Ring.toAddGroupWithOne.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@CommRing.toRing.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))) →
                  (D : Prod.{u_1, max (max u_2 u_4) u_1} G (Prod.{u_1, max u_2 u_4} G ((i : I) → M i)) → G) →
                    (hD :
                        ∀
                          (s :
                            @D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.Source.{u_1, u_2} G I
                              inst χ),
                          @Eq.{u_1 + 1} G
                            (D
                              (@D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.observe.{u_1, u_2,
                                    u_3, u_4}
                                G I C inst inst_1 M P χ s))
                            (@D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.target.{u_1, u_2} G
                              I inst inst_1 χ s)) →
                      @Finset.Nonempty.{u_2} I
                          (@D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.activeSenders.{u_1,
                                u_2, u_3, u_4}
                            G I C inst inst_1 M P χ) →
                        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                          Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.signature
                          PUnit.unit.{1} PUnit.unit.{1} :=
  fun {G : Type u_1} {I : Type u_2} {C : Type u_3} [inst : AddCommGroup.{u_1} G] [inst_1 : Fintype.{u_2} I]
    {M : I → Type u_4} [Nontrivial.{u_2} I]
    (P : D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.Protocol.{u_1, u_2, u_3, u_4} G I C M)
    (χ :
      @AddMonoidHom.{u_1, 0} G (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@AddZeroClass.toAddZero.{u_1} G
          (@AddMonoid.toAddZeroClass.{u_1} G
            (@SubNegMonoid.toAddMonoid.{u_1} G
              (@AddGroup.toSubNegMonoid.{u_1} G (@AddCommGroup.toAddGroup.{u_1} G inst)))))
        (@AddZeroClass.toAddZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@AddMonoidWithOne.toAddMonoid.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@AddGroupWithOne.toAddMonoidWithOne.{0}
                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
    (D : Prod.{u_1, max (max u_2 u_4) u_1} G (Prod.{u_1, max u_2 u_4} G ((i : I) → M i)) → G)
    (hD :
      ∀ (s : @D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.Source.{u_1, u_2} G I inst χ),
        @Eq.{u_1 + 1} G
          (D
            (@D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.observe.{u_1, u_2, u_3, u_4} G I C
              inst inst_1 M P χ s))
          (@D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.target.{u_1, u_2} G I inst inst_1 χ
            s))
    (a :
      @Finset.Nonempty.{u_2} I
        (@D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.activeSenders.{u_1, u_2, u_3, u_4} G I C
          inst inst_1 M P χ)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.signature
    Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.actual PUnit.unit.{1} PUnit.unit.{1}
    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
      (@Finset.card.{u_2} I
        (@D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.activeSenders.{u_1, u_2, u_3, u_4} G I C
          inst inst_1 M P χ))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))

noncomputable def Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.observationFact0.{u_1, u_2, u_3, u_4} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"ContextUpdates\",\"ExactSnapshotPeriodClassification\",\"period_classification\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"body\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"ContextUpdates\",\"ExactSnapshotPeriodClassification\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification, declaration := `D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.period_classification, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument, .argument, .argument, .argument, .body, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  { owner := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification, declaration := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.varyingLawInput.{u_1, u_2, u_3, u_4} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.canonicalArenaOperand.{u_1, u_2, u_3, u_4})
noncomputable def Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.varyingLaw.{u_1, u_2, u_3, u_4}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"ContextUpdates\",\"ExactSnapshotPeriodClassification\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}"

noncomputable def Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.statementExclusion.{u_1, u_2, u_3, u_4} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"ContextUpdates\",\"ExactSnapshotPeriodClassification\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ObserverMemory\",\"ContextUpdates\",\"ExactSnapshotPeriodClassification\",\"period_classification\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification, declaration := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  statementLocation := { owner := `D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification, declaration := `D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.period_classification, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration.{u_1, u_2, u_3, u_4}).actual (Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration.{u_1, u_2, u_3, u_4}).variation.2.choose (Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration.{u_1, u_2, u_3, u_4}).variation.1 (Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration.{u_1, u_2, u_3, u_4}).variation.2.choose_spec

noncomputable def Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"ContextUpdates\",\"ExactSnapshotPeriodClassification\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ObserverMemory\",\"ContextUpdates\",\"ExactSnapshotPeriodClassification\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification, declaration := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  { owner := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification, declaration := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  (by first | rfl | (ext <;> rfl))
