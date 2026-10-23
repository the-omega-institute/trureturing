import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Governance.LayeredLocalCacheSoundness
import Reg.Support.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Governance.LayeredLocalCacheSoundness

open _root_.D5.S3.ConceptDynamics.Governance.TraceKeyedArtifactCacheSoundness
open _root_.D5.S3.ConceptDynamics.Governance.LayeredLocalCacheSoundness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

abbrev signature : Signature where
  Params := Σ (M : Model.{u}), Σ (_ : Snapshot M.B.Node M.B.Src),
    Σ (_ : M.B.Node → List (Op M.B.Node M.B.Src)), Local M.B
  State p := Finset p.1.B.Node
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Result p.1.B
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The law includes semantic locality for every pair of local layers agreeing
on demand, as well as correctness, exact compilation work and probe readiness. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ (M : Model.{u}) (S : Snapshot M.B.Node M.B.Src) (_ : S ∈ M.snapshots)
    (schedule : M.B.Node → List (Op M.B.Node M.B.Src))
    (_ : ∀ n W m, Op.store W m ∈ schedule n → W ∈ M.snapshots)
    (L : Local M.B) (_ : Reachable M L) (roots : Finset M.B.Node),
    (planFor M.B S roots).roots = roots ∧
    Guarantees M S schedule L (planFor M.B S roots)
      (r.readout () ⟨M,S,schedule,L⟩ roots)

noncomputable def actual : Realization signature.{u} :=
  realize signature (fun _ p q => execute p.1.B p.2.1
    (fun n => run p.1.B (p.2.2.1 n)) p.2.2.2 (planFor p.1.B p.2.1 q).nodes)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => ⟨p.2.2.2, []⟩) (fun e => nomatch e)

abbrev tinySystem : BuildSystem.{u} :=
  ⟨PUnit, PUnit, PUnit, PUnit, PUnit, fun _ _ => ⟨⟩, fun _ _ => ⟨⟩, fun _ => ⟨⟩⟩

def tinySnapshot : Snapshot tinySystem.{u}.Node tinySystem.Src :=
  ⟨fun _ => ⟨⟩, fun _ => ∅, fun _ => 0, fun _ _ h => absurd h (Finset.notMem_empty _)⟩

abbrev tinyModel : Model.{u} where
  B := tinySystem
  snapshots := {tinySnapshot}
  noCollision := by
    intro X hX Y hY m n _
    have hx : X = tinySnapshot := hX
    have hy : Y = tinySnapshot := hY
    subst X Y
    exact ⟨rfl,rfl⟩

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let roots : Finset tinySystem.Node := {PUnit.unit}
  have actualLaw := layered_cache_contract tinyModel tinySnapshot (Set.mem_singleton _)
    (fun _ => []) (by intro n W m hm; simp at hm) (fun _ => none) Reachable.empty roots
  have bad := h tinyModel tinySnapshot (Set.mem_singleton _)
    (fun _ => []) (by intro n W m hm; simp at hm) (fun _ => none) Reachable.empty roots
  have mem : PUnit.unit ∈ (planFor tinySystem tinySnapshot roots).nodes := by
    apply ((planFor tinySystem tinySnapshot roots).exactDemand _).mpr
    apply Demand.root
    rw [actualLaw.1]
    exact Finset.mem_singleton_self _
  have visits := bad.2.visits
  change ([] : List tinySystem.Node) = (planFor tinySystem tinySnapshot roots).nodes at visits
  rw [← visits] at mem
  exact List.not_mem_nil mem

noncomputable def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨layered_cache_contract, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨tinyModel,tinySnapshot,fun _ => [],fun _ => none⟩,
      ({PUnit.unit} : Finset tinySystem.Node),(∅ : Finset tinySystem.Node),?_⟩
    intro h
    have full := layered_cache_contract tinyModel tinySnapshot (Set.mem_singleton _)
      (fun _ => []) (by intro n W m hm; simp at hm) (fun _ => none) Reachable.empty {PUnit.unit}
    have empty := layered_cache_contract tinyModel tinySnapshot (Set.mem_singleton _)
      (fun _ => []) (by intro n W m hm; simp at hm) (fun _ => none) Reachable.empty ∅
    have mem : PUnit.unit ∈ (planFor tinySystem tinySnapshot {PUnit.unit}).nodes := by
      apply ((planFor tinySystem tinySnapshot {PUnit.unit}).exactDemand _).mpr
      apply Demand.root
      rw [full.1]
      exact Finset.mem_singleton_self _
    have eq := congrArg (fun r : Result tinySystem => r.events.map Event.node) h
    change (execute tinySystem tinySnapshot
      (fun n => run tinySystem ((fun _ => []) n)) (fun _ => none)
      (planFor tinySystem tinySnapshot {PUnit.unit}).nodes).events.map Event.node =
      (execute tinySystem tinySnapshot (fun n => run tinySystem ((fun _ => []) n)) (fun _ => none)
      (planFor tinySystem tinySnapshot ∅).nodes).events.map Event.node at eq
    rw [full.2.visits,empty.2.visits] at eq
    rw [eq] at mem
    have demand := ((planFor tinySystem tinySnapshot ∅).exactDemand _).mp mem
    rw [empty.1] at demand
    have noDemand : ∀ n, Demand tinySystem tinySnapshot ∅ n → False := by
      intro n hn
      induction hn with
      | root hr => exact Finset.notMem_empty _ hr
      | dep _ _ ih => exact ih
    exact noDemand _ demand

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@layered_cache_contract.{u})
    (type_of% (realize.{u + 1,u,0,u,0} signature.{u}
      (fun _ p q => execute p.1.B p.2.1
        (fun n => run p.1.B (p.2.2.1 n)) p.2.2.2 (planFor p.1.B p.2.1 q).nodes)
      (fun e => nomatch e))) Unit Unit where
  unitName :=
    `D5.S3.ConceptDynamics.Governance.LayeredLocalCacheSoundness.layered_cache_contract.audit
  realizationName := `Reg.D5.S3.ConceptDynamics.Governance.LayeredLocalCacheSoundness.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{u + 1,u,0,u,0} signature.{u}
    (fun _ p q => execute p.1.B p.2.1
      (fun n => run p.1.B (p.2.2.1 n)) p.2.2.2 (planFor p.1.B p.2.1 q).nodes)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Governance.LayeredLocalCacheSoundness
    definition := none
    coordinates := #[0,1,3,5]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","arg","arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Reg.D5.S3.ConceptDynamics.Governance.LayeredLocalCacheSoundness
