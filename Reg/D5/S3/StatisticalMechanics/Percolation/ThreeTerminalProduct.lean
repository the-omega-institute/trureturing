import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The source is the actual union-network partition law on its complete cube. -/

set_option backward.isDefEq.respectTransparency.types false

namespace Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct

open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing
open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open SimpleGraph LeanInformationAudit

universe u v w
noncomputable section

structure Parameters where
  Vertices : Type u
  LeftEdges : Type v
  RightEdges : Type w
  finiteVertices : Fintype Vertices
  decidableVertices : DecidableEq Vertices
  finiteLeft : Fintype LeftEdges
  decidableLeft : DecidableEq LeftEdges
  finiteRight : Fintype RightEdges
  decidableRight : DecidableEq RightEdges
  leftEnds : LeftEdges → Vertices × Vertices
  rightEnds : RightEdges → Vertices × Vertices
  a : Vertices
  b : Vertices
  c : Vertices
  leftRate : LeftEdges → ℝ
  rightRate : RightEdges → ℝ

abbrev signature : Signature where
  Params := Parameters.{u,v,w}
  State _ := Mode
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v,w} := realize _
  (fun _ p => by
    letI := p.finiteVertices
    letI := p.decidableVertices
    letI := p.finiteLeft
    letI := p.decidableLeft
    letI := p.finiteRight
    letI := p.decidableRight
    exact law (Sum.elim p.leftEnds p.rightEnds) p.a p.b p.c
      (Sum.elim p.leftRate p.rightRate))
  (fun e => nomatch e)

def bad : Realization signature.{u,v,w} := realize _ (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law R := ∀ {V : Type u} {E : Type v} {F : Type w}
    [hV : Fintype V] [dV : DecidableEq V]
    [hE : Fintype E] [dE : DecidableEq E] [hF : Fintype F] [dF : DecidableEq F]
    (e : E → V × V) (f : F → V × V) (A B : Set V) (a b c g : V)
    (_h : OneVertexUnion (openGraph e (fun _ => true))
      (openGraph f (fun _ => true)) A B g)
    (_ha : a ∈ A) (_hb : b ∈ A) (_hc : c ∈ B)
    (θ : E → ℝ) (ρ : F → ℝ),
    let p := law e a b g θ
    let q := reliability f g c ρ
    R.readout () ⟨V,E,F,hV,dV,hE,dE,hF,dF,e,f,a,b,c,θ,ρ⟩ =
      fun s => match s with
      | .all => q*p .all
      | .ab => p .ab+(1-q)*p .all
      | .bc => q*p .bc
      | .ac => q*p .ac
      | .separate => p .separate+(1-q)*(p .bc+p .ac)

private theorem coincident_law {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (e : E → V × V) (a : V) (θ : E → ℝ) :
    law e a a a θ .all = 1 ∧ law e a a a θ .separate = 0 := by
  have hp (ω : E → Bool) : partition e a a a ω = .all := by
    simp [partition,connected]
  constructor
  · simp only [law,hp,ite_true]
    exact weight_sum θ
  · simp [law,hp]

private theorem coincident_reliability {V F : Type*} [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] (f : F → V × V) (a : V) (ρ : F → ℝ) :
    reliability f a a ρ = 1 := by
  simp only [reliability,connected,Reachable.rfl,decide_true,ite_true]
  exact weight_sum ρ

private theorem empty_union :
    OneVertexUnion
      (openGraph (fun e : PEmpty.{v+1} => nomatch e)
        (fun _ => true) : SimpleGraph PUnit.{u+1})
      (openGraph (fun e : PEmpty.{w+1} => nomatch e) (fun _ => true))
      Set.univ Set.univ PUnit.unit where
  left_support := fun {_ _} _ => ⟨trivial,trivial⟩
  right_support := fun {_ _} _ => ⟨trivial,trivial⟩
  intersection := fun {_} _ _ => Subsingleton.elim _ _

private theorem rejected : ¬ arena.{u,v,w}.Law bad := by
  classical
  intro h
  let e : PEmpty.{v+1} → PUnit.{u+1} × PUnit.{u+1} := fun x => nomatch x
  let f : PEmpty.{w+1} → PUnit.{u+1} × PUnit.{u+1} := fun x => nomatch x
  have hh := congrFun (h e f Set.univ Set.univ
    PUnit.unit PUnit.unit PUnit.unit PUnit.unit empty_union
    (by trivial) (by trivial) (by trivial) (fun _ => 0) (fun _ => 0)) .all
  change 0 = reliability f PUnit.unit PUnit.unit (fun _ => 0) *
    law e PUnit.unit PUnit.unit PUnit.unit (fun _ => 0) .all at hh
  rw [coincident_reliability,(coincident_law e PUnit.unit (fun _ => 0)).1] at hh
  norm_num at hh

private theorem dependence : ObservationalDependence signature.{u,v,w} actual := by
  classical
  intro i
  let e : PEmpty.{v+1} → PUnit.{u+1} × PUnit.{u+1} := fun x => nomatch x
  let f : PEmpty.{w+1} → PUnit.{u+1} × PUnit.{u+1} := fun x => nomatch x
  refine ⟨⟨PUnit,PEmpty,PEmpty,inferInstance,inferInstance,inferInstance,
    inferInstance,inferInstance,inferInstance,e,f,PUnit.unit,PUnit.unit,PUnit.unit,
    (fun _ => 0),(fun _ => 0)⟩,.all,.separate,?_⟩
  change law (Sum.elim e f) PUnit.unit PUnit.unit PUnit.unit
    (Sum.elim (fun _ => 0) (fun _ => 0)) .all ≠
    law (Sum.elim e f) PUnit.unit PUnit.unit PUnit.unit
      (Sum.elim (fun _ => 0) (fun _ => 0)) .separate
  obtain ⟨hall,hsep⟩ := coincident_law (Sum.elim e f) PUnit.unit
    (Sum.elim (fun _ => 0) (fun _ => 0))
  rw [hall,hsep]
  norm_num

def registration : Registration arena.{u,v,w} (type_of% @joined_network_law.{u,v,w}) where
  actual := actual
  bridge := by
    constructor
    · intro ht V E F hV dV hE dE hF dF e f A B a b c g h ha hb hc θ ρ
      dsimp only [actual,realize]
      refine Eq.trans (@ht V E F hV dV hE dE hF dF e f A B a b c g h ha hb hc θ ρ) ?_
      funext s
      cases s <;> rfl
    · intro ht V E F hV dV hE dE hF dF e f A B a b c g h ha hb hc θ ρ
      have hh := @ht V E F hV dV hE dE hF dF e f A B a b c g h ha hb hc θ ρ
      dsimp only [actual,realize] at hh
      refine Eq.trans hh ?_
      funext s
      cases s <;> rfl
  variation := ⟨by
    intro V E F hV dV hE dE hF dF e f A B a b c g h ha hb hc θ ρ
    dsimp only [actual,realize]
    refine Eq.trans (@joined_network_law V E F hV dV hE dE hF dF
      e f A B a b c g h ha hb hc θ ρ) ?_
    funext s
    cases s <;> rfl,bad,rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,?_,rejected⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def register_joined_network_law : Contract.Registration (@joined_network_law.{u,v,w})
    (Realization signature.{u,v,w}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.register_joined_network_law
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.registration
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
    (fun _ p => by
      letI := p.finiteVertices
      letI := p.decidableVertices
      letI := p.finiteLeft
      letI := p.decidableLeft
      letI := p.finiteRight
      letI := p.decidableRight
      exact law (Sum.elim p.leftEnds p.rightEnds) p.a p.b p.c
        (Sum.elim p.leftRate p.rightRate))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Cycle

structure Parameters where
  size : ℕ
  first : Fin (size + 3)
  second : Fin (size + 3)
  rate : Fin (size + 3) → ℝ

abbrev signature : Signature where
  Params := Parameters
  State _ := Mode
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _
  (fun _ p => law
    (_root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.cycleEnds p.size)
    0 p.first p.second p.rate)
  (fun e => nomatch e)

def bad : Realization signature := realize _
  (fun _ _ s => if s = .ab ∨ s = .bc then 1 else 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (i j : Fin (n + 3))
    (_hi : 0 < i.val) (_hij : i.val < j.val) (θ : Fin (n + 3) → ℝ)
    (_hθ : ∀ e, θ e ∈ Set.Icc 0 1),
    ∃ u v r : ℝ, u ∈ Set.Icc 0 1 ∧ v ∈ Set.Icc 0 1 ∧ r ∈ Set.Icc 0 1 ∧
      R.readout () ⟨n,i,j,θ⟩ =
        law _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms.triangleArmsEnds
          0 1 2 ![u,v,r,1,1,1] ∧
      0 ≤ delta (R.readout () ⟨n,i,j,θ⟩) ∧
      delta (R.readout () ⟨n,i,j,θ⟩)+
        R.readout () ⟨n,i,j,θ⟩ .all * R.readout () ⟨n,i,j,θ⟩ .ac ≤
        2*R.readout () ⟨n,i,j,θ⟩ .ac

private theorem rejected : ¬ arena.Law bad := by
  intro h
  obtain ⟨u,v,r,hu,hv,hr,heq,hlo,hup⟩ :=
    h (n:=0) 1 2 (by decide) (by decide) (fun _ => 0) (by intro e; norm_num)
  norm_num [bad,realize,delta] at hlo

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0,0,0,fun _ => 0⟩,.all,.separate,?_⟩
  change law
    (_root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.cycleEnds 0)
    0 0 0 (fun _ => 0) .all ≠
    law (_root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.cycleEnds 0)
      0 0 0 (fun _ => 0) .separate
  obtain ⟨hall,hsep⟩ := coincident_law
    (_root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.cycleEnds 0)
    0 (fun _ => 0)
  rw [hall,hsep]
  norm_num

def registration : Registration arena (type_of% @cycle_law_and_invariant) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cycle_law_and_invariant,bad,rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,?_,rejected⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def register_cycle_law_and_invariant : Contract.Registration (@cycle_law_and_invariant)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.Cycle.register_cycle_law_and_invariant
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.Cycle.registration
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
    (fun _ p => law
      (_root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs.cycleEnds p.size)
      0 p.first p.second p.rate)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.Cycle.register_cycle_law_and_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_cycle_law_and_invariant

end Cycle

/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.register_joined_network_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_joined_network_law

namespace Partition
structure Parameters where
  Vertices : Type u
  Edges : Type v
  finiteVertices : Fintype Vertices
  decidableVertices : DecidableEq Vertices
  finiteEdges : Fintype Edges
  ends : Edges → Vertices × Vertices
abbrev signature : Signature where
  Params := Parameters.{u,v}
  State p := (p.Vertices × p.Vertices × p.Vertices) × (p.Edges → Bool)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Mode
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u,v} := realize _ (fun _ p st => by
  letI := p.finiteVertices
  letI := p.decidableVertices
  letI := p.finiteEdges
  exact partition p.ends st.1.1 st.1.2.1 st.1.2.2 st.2) (fun e => nomatch e)
def bad : Realization signature.{u,v} := realize _ (fun _ _ _ => .ac) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {V : Type u} {E : Type v} [hV : Fintype V] [dV : DecidableEq V]
    [hE : Fintype E] (e : E → V × V) (a b c : V) (ω : E → Bool),
    R.readout () ⟨V,E,hV,dV,hE,e⟩ ((a,b,c),ω) =
      _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.graphMode
        (openGraph e ω) a b c
private theorem rejected : ¬ arena.{u,v}.Law bad := by
  intro h
  have hh := h (fun x : PEmpty.{v+1} => (nomatch x : PUnit.{u+1} × PUnit.{u+1}))
    PUnit.unit PUnit.unit PUnit.unit (fun x => nomatch x)
  simpa [bad,realize,_root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.graphMode] using hh
private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  classical
  intro i
  let a : ULift.{u} Bool := ⟨false⟩
  let b : ULift.{u} Bool := ⟨true⟩
  let e : PEmpty.{v+1} → ULift.{u} Bool × ULift.{u} Bool := fun x => nomatch x
  let ω : PEmpty.{v+1} → Bool := fun x => nomatch x
  refine ⟨⟨ULift Bool,PEmpty,inferInstance,inferInstance,inferInstance,e⟩,
    ((a,a,a),ω),((a,b,a),ω),?_⟩
  change partition e a a a ω ≠ partition e a b a ω
  rw [partition_graphMode,partition_graphMode]
  have hg : openGraph e ω = ⊥ := by ext x y; simp [openGraph,e]
  simp [hg,_root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTree.graphMode,a,b]
def registration : Registration arena.{u,v} (type_of% @partition_graphMode.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨partition_graphMode,bad,rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,?_,rejected⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence
def register_partition_graphMode : Contract.Registration (@partition_graphMode.{u,v})
    (Realization signature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.Partition.register_partition_graphMode
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.Partition.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p st => by
    letI := p.finiteVertices
    letI := p.decidableVertices
    letI := p.finiteEdges
    exact partition p.ends st.1.1 st.1.2.1 st.1.2.2 st.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.Partition.register_partition_graphMode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_partition_graphMode
end Partition

open _root_.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalAttachment

private theorem one_sensitivity {S : Signature} (L : Realization S → Prop)
    (actual bad : Realization S) [Subsingleton S.Role] [IsEmpty S.Anchor]
    (hbad : ¬ L bad) : Sensitivity ⟨S,L⟩ actual := by
  constructor
  · intro i
    refine ⟨bad,?_,?_,hbad⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact isEmptyElim e
  · intro e
    exact isEmptyElim e

private theorem coincident_source {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (e : E → V × V) (a : V) (θ : E → ℝ) :
    law e a a a θ = fun s => if s = .all then 1 else 0 := by
  have hp (ω : E → Bool) : partition e a a a ω = .all := by
    simp [partition,connected]
  funext s
  unfold law
  simp only [hp]
  by_cases hs : s = .all
  · subst s
    simpa only [ite_true] using weight_sum θ
  · simp [hs,Ne.symm hs]

namespace Transfer
abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law R := ∀ {V : Type u} {E : Type v} {F : Type w}
    [hV : Fintype V] [dV : DecidableEq V]
    [hE : Fintype E] [dE : DecidableEq E] [hF : Fintype F] [dF : DecidableEq F]
    (e : E → V × V) (f : F → V × V) (A B : Set V) (a b c g : V)
    (_h : OneVertexUnion (openGraph e (fun _ => true))
      (openGraph f (fun _ => true)) A B g) (port : Port)
    (_hs : Supported port A B a b c) (θ : E → ℝ) (ρ : F → ℝ),
    R.readout () ⟨V,E,F,hV,dV,hE,dE,hF,dF,e,f,a,b,c,θ,ρ⟩ =
      transfer port (law e (gateTerminals port a b c g).1
        (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2 θ)
        (reliability f g (outerTerminal port a b c) ρ)
private theorem rejected : ¬ arena.{u,v,w}.Law bad := by
  classical
  intro h
  let e : PEmpty.{v+1} → PUnit.{u+1} × PUnit.{u+1} := fun x => nomatch x
  let f : PEmpty.{w+1} → PUnit.{u+1} × PUnit.{u+1} := fun x => nomatch x
  have hs : Supported .c Set.univ Set.univ PUnit.unit PUnit.unit PUnit.unit :=
    ⟨trivial,trivial,trivial⟩
  have hh := congrFun (h e f Set.univ Set.univ
    PUnit.unit PUnit.unit PUnit.unit PUnit.unit empty_union .c hs
    (fun _ => 0) (fun _ => 0)) .all
  have ho := congrFun (joined_network_transfer e f Set.univ Set.univ
    PUnit.unit PUnit.unit PUnit.unit PUnit.unit empty_union .c hs
    (fun _ => 0) (fun _ => 0)) .all
  change 0 = _ at hh
  rw [← ho,(coincident_law (Sum.elim e f) PUnit.unit
    (Sum.elim (fun _ => 0) (fun _ => 0))).1] at hh
  norm_num at hh
def registration : Registration arena.{u,v,w} (type_of% @joined_network_transfer.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨joined_network_transfer,bad,rejected⟩
  sensitivity := one_sensitivity _ actual bad rejected
  dependence := dependence

def register_joined_network_transfer : Contract.Registration (@joined_network_transfer.{u,v,w})
    (Realization signature.{u,v,w}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.Transfer.register_joined_network_transfer
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.Transfer.registration
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
    (fun _ p => by
      letI := p.finiteVertices
      letI := p.decidableVertices
      letI := p.finiteLeft
      letI := p.decidableLeft
      letI := p.finiteRight
      letI := p.decidableRight
      exact law (Sum.elim p.leftEnds p.rightEnds) p.a p.b p.c
        (Sum.elim p.leftRate p.rightRate)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.Transfer.register_joined_network_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_joined_network_transfer
end Transfer

namespace Ignored
abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law R := ∀ {V : Type u} {E : Type v} {F : Type w}
    [hV : Fintype V] [dV : DecidableEq V]
    [hE : Fintype E] [dE : DecidableEq E] [hF : Fintype F] [dF : DecidableEq F]
    (e : E → V × V) (f : F → V × V) (A B : Set V) (a b c g : V)
    (_h : OneVertexUnion (openGraph e (fun _ => true))
      (openGraph f (fun _ => true)) A B g)
    (_ha : a ∈ A) (_hb : b ∈ A) (_hc : c ∈ A) (_hg : g ∈ B)
    (θ : E → ℝ) (ρ : F → ℝ),
    R.readout () ⟨V,E,F,hV,dV,hE,dE,hF,dF,e,f,a,b,c,θ,ρ⟩ = law e a b c θ
private theorem rejected : ¬ arena.{u,v,w}.Law bad := by
  classical
  intro h
  let e : PEmpty.{v+1} → PUnit.{u+1} × PUnit.{u+1} := fun x => nomatch x
  let f : PEmpty.{w+1} → PUnit.{u+1} × PUnit.{u+1} := fun x => nomatch x
  have hh := congrFun (h e f Set.univ Set.univ
    PUnit.unit PUnit.unit PUnit.unit PUnit.unit empty_union
    (by trivial) (by trivial) (by trivial) (by trivial)
    (fun _ => 0) (fun _ => 0)) .all
  change 0 = law e PUnit.unit PUnit.unit PUnit.unit (fun _ => 0) .all at hh
  rw [(coincident_law e PUnit.unit (fun _ => 0)).1] at hh
  norm_num at hh
def registration : Registration arena.{u,v,w} (type_of% @joined_network_ignored.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨joined_network_ignored,bad,rejected⟩
  sensitivity := one_sensitivity _ actual bad rejected
  dependence := dependence

def register_joined_network_ignored : Contract.Registration (@joined_network_ignored.{u,v,w})
    (Realization signature.{u,v,w}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.Ignored.register_joined_network_ignored
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.Ignored.registration
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
    (fun _ p => by
      letI := p.finiteVertices
      letI := p.decidableVertices
      letI := p.finiteLeft
      letI := p.decidableLeft
      letI := p.finiteRight
      letI := p.decidableRight
      exact law (Sum.elim p.leftEnds p.rightEnds) p.a p.b p.c
        (Sum.elim p.leftRate p.rightRate)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.Ignored.register_joined_network_ignored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_joined_network_ignored
end Ignored

namespace Invariant
def negative : Realization signature.{u,v,w} := realize _
  (fun _ _ s => if s = .ab ∨ s = .bc then 1 else 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law R := ∀ {V : Type u} {E : Type v} {F : Type w}
    [hV : Fintype V] [dV : DecidableEq V]
    [hE : Fintype E] [dE : DecidableEq E] [hF : Fintype F] [dF : DecidableEq F]
    (e : E → V × V) (f : F → V × V) (A B : Set V) (a b c g : V)
    (_h : OneVertexUnion (openGraph e (fun _ => true))
      (openGraph f (fun _ => true)) A B g) (port : Port)
    (_hs : Supported port A B a b c) (θ : E → ℝ) (ρ : F → ℝ)
    (_hθ : ∀ i, θ i ∈ Set.Icc 0 1) (_hρ : ∀ i, ρ i ∈ Set.Icc 0 1)
    (C : ℝ) (_hC : 1 ≤ C),
    let p := law e (gateTerminals port a b c g).1
      (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2 θ
    0 ≤ delta p → delta p+p .all*p .ac ≤ C*p .ac →
    0 ≤ delta (R.readout () ⟨V,E,F,hV,dV,hE,dE,hF,dF,e,f,a,b,c,θ,ρ⟩) ∧
      delta (R.readout () ⟨V,E,F,hV,dV,hE,dE,hF,dF,e,f,a,b,c,θ,ρ⟩)+
        R.readout () ⟨V,E,F,hV,dV,hE,dE,hF,dF,e,f,a,b,c,θ,ρ⟩ .all *
        R.readout () ⟨V,E,F,hV,dV,hE,dE,hF,dF,e,f,a,b,c,θ,ρ⟩ .ac ≤ C*R.readout () ⟨V,E,F,hV,dV,hE,dE,hF,dF,e,f,a,b,c,θ,ρ⟩ .ac
private theorem rejected : ¬ arena.{u,v,w}.Law negative := by
  classical
  intro h
  let e : PEmpty.{v+1} → PUnit.{u+1} × PUnit.{u+1} := fun x => nomatch x
  let f : PEmpty.{w+1} → PUnit.{u+1} × PUnit.{u+1} := fun x => nomatch x
  have hs : Supported .c Set.univ Set.univ PUnit.unit PUnit.unit PUnit.unit :=
    ⟨trivial,trivial,trivial⟩
  have hlo : 0 ≤ delta (law e PUnit.unit PUnit.unit PUnit.unit (fun _ => 0)) := by
    rw [coincident_source]
    norm_num [delta]
  have hbound : delta (law e PUnit.unit PUnit.unit PUnit.unit (fun _ => 0))+
      law e PUnit.unit PUnit.unit PUnit.unit (fun _ => 0) .all *
      law e PUnit.unit PUnit.unit PUnit.unit (fun _ => 0) .ac ≤
      1*law e PUnit.unit PUnit.unit PUnit.unit (fun _ => 0) .ac := by
    rw [coincident_source]
    norm_num [delta]
  have hh := (h e f Set.univ Set.univ
    PUnit.unit PUnit.unit PUnit.unit PUnit.unit empty_union .c hs
    (fun _ => 0) (fun _ => 0) (by intro x; exact nomatch x)
    (by intro x; exact nomatch x) 1 le_rfl hlo hbound).1
  norm_num [negative,realize,delta] at hh
def registration : Registration arena.{u,v,w} (type_of% @joined_network_invariant.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨joined_network_invariant,negative,rejected⟩
  sensitivity := one_sensitivity _ actual negative rejected
  dependence := dependence

def register_joined_network_invariant : Contract.Registration (@joined_network_invariant.{u,v,w})
    (Realization signature.{u,v,w}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.Invariant.register_joined_network_invariant
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.Invariant.registration
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
    (fun _ p => by
      letI := p.finiteVertices
      letI := p.decidableVertices
      letI := p.finiteLeft
      letI := p.decidableLeft
      letI := p.finiteRight
      letI := p.decidableRight
      exact law (Sum.elim p.leftEnds p.rightEnds) p.a p.b p.c
        (Sum.elim p.leftRate p.rightRate)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.Invariant.register_joined_network_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_joined_network_invariant
end Invariant

namespace SignedInvariant
abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law R := ∀ {V : Type u} {E : Type v} {F : Type w}
    [hV : Fintype V] [dV : DecidableEq V]
    [hE : Fintype E] [dE : DecidableEq E] [hF : Fintype F] [dF : DecidableEq F]
    (e : E → V × V) (f : F → V × V) (A B : Set V) (a b c g : V)
    (_h : OneVertexUnion (openGraph e (fun _ => true))
      (openGraph f (fun _ => true)) A B g) (port : Port)
    (_hs : Supported port A B a b c) (θ : E → ℝ) (ρ : F → ℝ)
    (_hθ : ∀ i, θ i ∈ Set.Icc 0 1) (_hρ : ∀ i, ρ i ∈ Set.Icc 0 1)
    (C : ℝ) (_hC : 1 ≤ C),
    let p := law e (gateTerminals port a b c g).1
      (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2 θ
    |delta p|+p .all*p .ac ≤ C*p .ac →
    |delta (R.readout () ⟨V,E,F,hV,dV,hE,dE,hF,dF,e,f,a,b,c,θ,ρ⟩)|+
        R.readout () ⟨V,E,F,hV,dV,hE,dE,hF,dF,e,f,a,b,c,θ,ρ⟩ .all *
        R.readout () ⟨V,E,F,hV,dV,hE,dE,hF,dF,e,f,a,b,c,θ,ρ⟩ .ac ≤ C*R.readout () ⟨V,E,F,hV,dV,hE,dE,hF,dF,e,f,a,b,c,θ,ρ⟩ .ac
private theorem rejected : ¬ arena.{u,v,w}.Law Invariant.negative := by
  classical
  intro h
  let e : PEmpty.{v+1} → PUnit.{u+1} × PUnit.{u+1} := fun x => nomatch x
  let f : PEmpty.{w+1} → PUnit.{u+1} × PUnit.{u+1} := fun x => nomatch x
  have hs : Supported .c Set.univ Set.univ PUnit.unit PUnit.unit PUnit.unit :=
    ⟨trivial,trivial,trivial⟩
  have hbound : |delta (law e PUnit.unit PUnit.unit PUnit.unit (fun _ => 0))|+
      law e PUnit.unit PUnit.unit PUnit.unit (fun _ => 0) .all *
      law e PUnit.unit PUnit.unit PUnit.unit (fun _ => 0) .ac ≤
      1*law e PUnit.unit PUnit.unit PUnit.unit (fun _ => 0) .ac := by
    rw [coincident_source]
    norm_num [delta]
  have hh := h e f Set.univ Set.univ
    PUnit.unit PUnit.unit PUnit.unit PUnit.unit empty_union .c hs
    (fun _ => 0) (fun _ => 0) (by intro x; exact nomatch x)
    (by intro x; exact nomatch x) 1 le_rfl hbound
  norm_num [Invariant.negative,realize,delta] at hh
def registration : Registration arena.{u,v,w} (type_of% @joined_network_signed_invariant.{u,v,w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨joined_network_signed_invariant,Invariant.negative,rejected⟩
  sensitivity := one_sensitivity _ actual Invariant.negative rejected
  dependence := dependence

def register_joined_network_signed_invariant : Contract.Registration (@joined_network_signed_invariant.{u,v,w})
    (Realization signature.{u,v,w}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.SignedInvariant.register_joined_network_signed_invariant
  realizationName := `Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.SignedInvariant.registration
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
    (fun _ p => by
      letI := p.finiteVertices
      letI := p.decidableVertices
      letI := p.finiteLeft
      letI := p.decidableLeft
      letI := p.finiteRight
      letI := p.decidableRight
      exact law (Sum.elim p.leftEnds p.rightEnds) p.a p.b p.c
        (Sum.elim p.leftRate p.rightRate)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
/-- info: 'Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.SignedInvariant.register_joined_network_signed_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms register_joined_network_signed_invariant
end SignedInvariant

end
end Reg.D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct
