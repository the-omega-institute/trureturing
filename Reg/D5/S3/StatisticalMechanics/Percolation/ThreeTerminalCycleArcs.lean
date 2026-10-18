import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Four-slot registrations retain the cycle configurations and their actual graph observations. -/

set_option backward.isDefEq.respectTransparency.types false

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit SimpleGraph
noncomputable section

private theorem single_sensitivity {S : Signature} (actual bad : Realization S)
    (L : Realization S → Prop) (hbad : ¬ L bad) [Subsingleton S.Role] [IsEmpty S.Anchor] :
    Sensitivity ⟨S,L⟩ actual := by
  constructor
  · intro i
    refine ⟨bad,?_,?_,hbad⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact isEmptyElim e
  · intro e
    exact isEmptyElim e

namespace Reachability
structure Parameters where
  n : ℕ
  configuration : Fin (n + 3) → Bool
abbrev signature : Signature where
  Params := Parameters
  State p := Fin (p.n + 3) × Fin (p.n + 3)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _
  (fun _ p s => connected (cycleEnds p.n) p.configuration s.1 s.2) (fun e => nomatch e)
def bad : Realization signature := realize _ (fun _ _ _ => true) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (ω : Fin (n + 3) → Bool) (l r : Fin (n + 3))
    (_hlr : l.val < r.val), R.readout () ⟨n,ω⟩ (l,r) = true ↔
      (∀ e : Fin (n + 3), l.val ≤ e.val → e.val < r.val → ω e = true) ∨
      (∀ e : Fin (n + 3), e.val < l.val ∨ r.val ≤ e.val → ω e = true)
private theorem rejected : ¬ arena.Law bad := by
  intro h
  have hh := h (n:=0) (fun _ => false) 0 1 (by decide)
  have hright := hh.mp (by rfl)
  rcases hright with hright | hright
  · have hh := hright 0 (by decide) (by decide)
    cases hh
  · have hh := hright 1 (Or.inr (by decide))
    cases hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,fun _ => false⟩,(0,0),(0,1),?_⟩
  change connected (cycleEnds 0) (fun _ => false) 0 0 ≠
    connected (cycleEnds 0) (fun _ => false) 0 1
  decide +kernel

def registration : Registration arena (type_of% @cycle_reachable_iff) where
  actual := actual
  bridge := by simp only [arena,actual,realize,connected,decide_eq_true_eq]
  variation := ⟨by simpa only [actual,realize,connected,decide_eq_true_eq] using
    @cycle_reachable_iff,bad,rejected⟩
  sensitivity := single_sensitivity actual bad _ rejected
  dependence := dependence

def register_cycle_reachable_iff : Contract.Registration (@cycle_reachable_iff)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.Reachability.register_cycle_reachable_iff
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.Reachability.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p s => connected (cycleEnds p.n) p.configuration s.1 s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reachability

namespace Partition
structure Parameters where
  n : ℕ
  configuration : Fin (n + 3) → Bool
abbrev signature : Signature where
  Params := Parameters
  State p := Fin (p.n + 3) × Fin (p.n + 3) × Fin (p.n + 3)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Mode
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _
  (fun _ p s => partition (cycleEnds p.n) s.1 s.2.1 s.2.2 p.configuration)
  (fun e => nomatch e)
def bad : Realization signature := realize _ (fun _ _ _ => .all) (fun e => nomatch e)
private theorem graphMode_eq_partition {n : ℕ} (ω : Fin (n + 3) → Bool)
    (a b c : Fin (n + 3)) : graphMode (openGraph (cycleEnds n) ω) a b c =
      partition (cycleEnds n) a b c ω := by
  simp only [graphMode,partition,connected,decide_eq_true_eq]
  all_goals
    by_cases hab : (openGraph (cycleEnds n) ω).Reachable a b <;>
      by_cases hbc : (openGraph (cycleEnds n) ω).Reachable b c <;>
      by_cases hac : (openGraph (cycleEnds n) ω).Reachable a c <;> simp_all
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (ω : Fin (n + 3) → Bool) (i j : Fin (n + 3))
    (_hi : 0 < i.val) (_hij : i.val < j.val),
    R.readout () ⟨n,ω⟩ (0,i,j) = partition triangleArmsEnds 0 1 2
      ![arcBit ω 0 i.val,arcBit ω i.val j.val,arcBit ω j.val (n + 3),true,true,true]
private theorem rejected : ¬ arena.Law bad := by
  intro h
  have hh := h (n:=0) (fun _ => false) 1 2 (by decide) (by decide)
  change Mode.all = _ at hh
  have hh' : Mode.all = Mode.separate := hh.trans (by decide +kernel)
  cases hh'
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,fun _ => false⟩,(0,0,0),(0,1,2),?_⟩
  change partition (cycleEnds 0) 0 0 0 (fun _ => false) ≠
    partition (cycleEnds 0) 0 1 2 (fun _ => false)
  decide +kernel

def registration : Registration arena (type_of% @cycle_partition) where
  actual := actual
  bridge := by simp only [arena,actual,realize,← graphMode_eq_partition]
  variation := ⟨by simpa only [actual,realize,← graphMode_eq_partition] using
    @cycle_partition,bad,rejected⟩
  sensitivity := single_sensitivity actual bad _ rejected
  dependence := dependence

def register_cycle_partition : Contract.Registration (@cycle_partition)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.Partition.register_cycle_partition
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.Partition.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p s => partition (cycleEnds p.n) s.1 s.2.1 s.2.2 p.configuration)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Partition

namespace Support
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Finset (Fin (n + 3))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _
  (fun _ n s => arcSupport n s.1 s.2) (fun e => nomatch e)
def bad : Realization signature := realize _ (fun _ _ _ => Finset.univ) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (i j : Fin (n + 3)) (_hij : i.val ≤ j.val),
    Disjoint (R.readout () n (0,i.val)) (R.readout () n (i.val,j.val)) ∧
    Disjoint (R.readout () n (0,i.val)) (R.readout () n (j.val,n + 3)) ∧
    Disjoint (R.readout () n (i.val,j.val)) (R.readout () n (j.val,n + 3)) ∧
    R.readout () n (0,i.val) ∪ R.readout () n (i.val,j.val) ∪
      R.readout () n (j.val,n + 3) = Finset.univ
private theorem rejected : ¬ arena.Law bad := by
  intro h
  have hh := (h (n:=0) 1 2 (by decide)).1
  exact Finset.disjoint_left.mp hh (Finset.mem_univ (0 : Fin 3)) (Finset.mem_univ 0)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0,(0,0),(0,1),?_⟩
  change arcSupport 0 0 0 ≠ arcSupport 0 0 1
  decide +kernel

def registration : Registration arena (type_of% @arcSupport_partition) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨arcSupport_partition,bad,rejected⟩
  sensitivity := single_sensitivity actual bad _ rejected
  dependence := dependence

def register_arcSupport_partition : Contract.Registration (@arcSupport_partition)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.Support.register_arcSupport_partition
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.Support.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ n s => arcSupport n s.1 s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Support

namespace WalkPartition
universe u
structure Parameters where
  Vertices : Type u
  graph : SimpleGraph Vertices
  base : Vertices
  walk : graph.Walk base base
  n : ℕ
  configuration : Fin (n + 3) → Bool
abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Fin (p.n + 3) × Fin (p.n + 3) × Fin (p.n + 3)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Mode
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize _
  (fun _ p s => graphMode (openGraph (fun e : Fin (p.n + 3) =>
    (p.walk.getVert e.val,p.walk.getVert (e.val+1))) p.configuration)
    (p.walk.getVert s.1.val) (p.walk.getVert s.2.1.val) (p.walk.getVert s.2.2.val))
  (fun e => nomatch e)
def bad : Realization signature.{u} := realize _ (fun _ _ _ => .all) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} {G : SimpleGraph V} {a : V}
    (p : G.Walk a a) (_hp : p.IsCycle) {n : ℕ} (_hlen : p.length = n + 3)
    (ω : Fin (n + 3) → Bool) (i j : Fin (n + 3)) (_hi : 0 < i.val) (_hij : i.val < j.val),
    R.readout () ⟨V,G,a,p,n,ω⟩ (0,i,j) = partition triangleArmsEnds 0 1 2
      ![arcBit ω 0 i.val,arcBit ω i.val j.val,arcBit ω j.val (n + 3),true,true,true]

private def triWalk : (⊤ : SimpleGraph (ULift.{u} (Fin 3))).Walk
    (ULift.up 0) (ULift.up 0) :=
  let h01 : (⊤ : SimpleGraph (ULift.{u} (Fin 3))).Adj (ULift.up 0) (ULift.up 1) := by simp
  let h12 : (⊤ : SimpleGraph (ULift.{u} (Fin 3))).Adj (ULift.up 1) (ULift.up 2) := by simp
  let h20 : (⊤ : SimpleGraph (ULift.{u} (Fin 3))).Adj (ULift.up 2) (ULift.up 0) := by simp
  .cons h01 (.cons h12 (.cons h20 .nil))

private theorem triWalk_cycle : (triWalk.{u}).IsCycle := by
  simp [triWalk,Walk.cons_isCycle_iff,Walk.isPath_def,Walk.edges_cons,Sym2.eq_iff]

private theorem rejected : ¬ arena.{u}.Law bad := by
  intro h
  have hh := h triWalk triWalk_cycle (n:=0) rfl (fun _ => false) 1 2
    (by decide) (by decide)
  change Mode.all = _ at hh
  have hh' : Mode.all = Mode.separate := hh.trans (by decide +kernel)
  cases hh'

private theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro i
  refine ⟨⟨ULift (Fin 3),⊤,ULift.up 0,triWalk,0,fun _ => false⟩,
    (0,0,0),(0,1,2),?_⟩
  have hempty : openGraph (fun e : Fin 3 =>
      (triWalk.getVert e.val,triWalk.getVert (e.val+1))) (fun _ => false) = ⊥ := by
    ext a b
    simp [openGraph,SimpleGraph.fromRel_adj]
  change graphMode _ _ _ _ ≠ graphMode _ _ _ _
  rw [hempty]
  simp [graphMode,triWalk]

def registration : Registration arena.{u} (type_of% @walk_cycle_partition.{u}) where
  actual := actual
  bridge := by simp only [arena,actual,realize,Fin.val_zero,Walk.getVert_zero]
  variation := ⟨by simpa only [actual,realize,Fin.val_zero,Walk.getVert_zero] using
    @walk_cycle_partition.{u},bad,rejected⟩
  sensitivity := single_sensitivity actual bad _ rejected
  dependence := dependence

def register_walk_cycle_partition : Contract.Registration (@walk_cycle_partition.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.WalkPartition.register_walk_cycle_partition
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.WalkPartition.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p s => graphMode (openGraph (fun e : Fin (p.n + 3) =>
      (p.walk.getVert e.val,p.walk.getVert (e.val+1))) p.configuration)
      (p.walk.getVert s.1.val) (p.walk.getVert s.2.1.val) (p.walk.getVert s.2.2.val))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end WalkPartition

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.Reachability.register_cycle_reachable_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reachability.register_cycle_reachable_iff

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.Partition.register_cycle_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Partition.register_cycle_partition

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.Support.register_arcSupport_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Support.register_arcSupport_partition

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.WalkPartition.register_walk_cycle_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WalkPartition.register_walk_cycle_partition


namespace BondPartition
universe u
structure Parameters where
  Vertices : Type u
  graph : SimpleGraph Vertices
  configuration : graph.edgeSet → Bool
abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.Vertices × p.Vertices × p.Vertices
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Mode
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize _
  (fun _ p s => graphMode (bondGraph p.graph p.configuration) s.1 s.2.1 s.2.2)
  (fun e => nomatch e)
def bad : Realization signature.{u} := realize _ (fun _ _ _ => .all) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} {G : SimpleGraph V} {a : V}
    (p : G.Walk a a) (hp : p.IsCycle) {n : ℕ} (hlen : p.length = n + 3)
    (hedges : G.edgeSet = p.edgeSet) (ω : G.edgeSet → Bool)
    (i j : Fin (n + 3)) (_hi : 0 < i.val) (_hij : i.val < j.val),
    let ξ := fun e => ω (cycleEdgeEquiv p hp hlen hedges e)
    R.readout () ⟨V,G,ω⟩ (a,p.getVert i.val,p.getVert j.val) =
      partition triangleArmsEnds 0 1 2
        ![arcBit ξ 0 i.val,arcBit ξ i.val j.val,arcBit ξ j.val (n + 3),true,true,true]

private theorem triWalk_edges :
    (⊤ : SimpleGraph (ULift.{u} (Fin 3))).edgeSet = WalkPartition.triWalk.edgeSet := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
    fin_cases x <;> fin_cases y <;>
      simp [WalkPartition.triWalk,Walk.edgeSet,Sym2.eq_iff]

private theorem rejected : ¬ arena.{u}.Law bad := by
  intro h
  have hh := h WalkPartition.triWalk WalkPartition.triWalk_cycle (n:=0) rfl
    triWalk_edges (fun _ => false) 1 2 (by decide) (by decide)
  change Mode.all = _ at hh
  have hh' : Mode.all = Mode.separate := hh.trans (by decide +kernel)
  cases hh'

private theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro i
  let V := ULift.{u} (Fin 3)
  let G : SimpleGraph V := ⊤
  refine ⟨⟨V,G,fun _ => false⟩,(ULift.up 0,ULift.up 0,ULift.up 0),
    (ULift.up 0,ULift.up 1,ULift.up 2),?_⟩
  have hempty : bondGraph G (fun _ => false) = ⊥ := by
    ext a b
    simp [bondGraph,SimpleGraph.fromEdgeSet_adj]
  change graphMode (bondGraph G _) _ _ _ ≠ graphMode (bondGraph G _) _ _ _
  rw [hempty]
  simp only [graphMode,SimpleGraph.reachable_bot]
  decide +kernel

def registration : Registration arena.{u} (type_of% @bond_cycle_partition.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bond_cycle_partition,bad,rejected⟩
  sensitivity := single_sensitivity actual bad _ rejected
  dependence := dependence

def register_bond_cycle_partition : Contract.Registration (@bond_cycle_partition.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.BondPartition.register_bond_cycle_partition
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.BondPartition.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p s => graphMode (bondGraph p.graph p.configuration) s.1 s.2.1 s.2.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end BondPartition

namespace Core
abbrev signature : Signature where
  Params := Unit
  State _ := Fin 3 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Mode
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _
  (fun _ _ s => partition triangleArmsEnds 0 1 2 ![s 0,s 1,s 2,true,true,true])
  (fun e => nomatch e)
def bad : Realization signature := realize _ (fun _ _ _ => .all) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p q r : Bool, R.readout () () ![p,q,r] =
    if p || (q && r) then
      (if q || (p && r) then .all else .ab)
    else if q || (p && r) then .bc
    else if r || (p && q) then .ac else .separate
private theorem rejected : ¬ arena.Law bad := by
  intro h
  have hh := h false false false
  cases hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),![false,false,false],![true,true,true],?_⟩
  change partition triangleArmsEnds 0 1 2 ![false,false,false,true,true,true] ≠
    partition triangleArmsEnds 0 1 2 ![true,true,true,true,true,true]
  decide +kernel

def registration : Registration arena (type_of% @core_partition) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨core_partition,bad,rejected⟩
  sensitivity := single_sensitivity actual bad _ rejected
  dependence := dependence

def register_core_partition : Contract.Registration (@core_partition)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.Core.register_core_partition
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.Core.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ s => partition triangleArmsEnds 0 1 2 ![s 0,s 1,s 2,true,true,true])
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Core
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.BondPartition.register_bond_cycle_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BondPartition.register_bond_cycle_partition

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.Core.register_core_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Core.register_core_partition


namespace Coordinates
universe u
structure Parameters where
  Vertices : Type u
  graph : SimpleGraph Vertices
  base : Vertices
  walk : graph.Walk base base
abbrev signature : Signature where
  Params := Parameters.{u}
  State p := ℕ × p.Vertices
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize _
  (fun _ p s => @decide (p.walk.getVert s.1 = s.2) (Classical.propDecidable _))
  (fun e => nomatch e)
def bad : Realization signature.{u} := realize _ (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (_hp : p.IsCycle) (a b c : V)
    (_ha : a ∈ p.support) (_hb : b ∈ p.support) (_hc : c ∈ p.support)
    (_hab : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c),
    ∃ (q : G.Walk a a) (_hq : q.IsCycle) (n : ℕ) (_hlen : q.length = n + 3)
      (_hedges : q.edgeSet = p.edgeSet) (i j : Fin (n + 3)),
      0 < i.val ∧ i.val < j.val ∧
      R.readout () ⟨V,G,a,q⟩ (i.val,b) = true ∧ R.readout () ⟨V,G,a,q⟩ (j.val,c) = true
private theorem rejected : ¬ arena.{u}.Law bad := by
  intro h
  have hh := h WalkPartition.triWalk WalkPartition.triWalk_cycle
    (ULift.up 0) (ULift.up 1) (ULift.up 2)
    (by simp [WalkPartition.triWalk]) (by simp [WalkPartition.triWalk])
    (by simp [WalkPartition.triWalk]) (by simp) (by simp) (by simp)
  obtain ⟨q,hq,n,hlen,hedges,i,j,hi,hij,hb,hc⟩ := hh
  cases hb
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift (Fin 3),⊤,ULift.up 0,WalkPartition.triWalk⟩,
    (0,ULift.up 0),(0,ULift.up 1),?_⟩
  simp [actual,realize,WalkPartition.triWalk]

def registration : Registration arena.{u} (type_of% @cycle_ordered_coordinates.{u}) where
  actual := actual
  bridge := by simp only [arena,actual,realize,decide_eq_true_eq]
  variation := ⟨by simpa only [actual,realize,decide_eq_true_eq] using
    @cycle_ordered_coordinates.{u},bad,rejected⟩
  sensitivity := single_sensitivity actual bad _ rejected
  dependence := dependence

def register_cycle_ordered_coordinates : Contract.Registration (@cycle_ordered_coordinates.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.Coordinates.register_cycle_ordered_coordinates
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.Coordinates.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p s => @decide (p.walk.getVert s.1 = s.2) (Classical.propDecidable _))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Coordinates

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.Coordinates.register_cycle_ordered_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Coordinates.register_cycle_ordered_coordinates

end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs
