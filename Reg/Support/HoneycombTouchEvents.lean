import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch
import Reg.Support.SingleDependentReadout

/-! Dependent-family registrations for synchronous touch events on universe-polymorphic graphs. -/

namespace Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination (Vertex honeycombGraph)
open _root_.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch


set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

attribute [local instance] repositoryAdjacency

universe u o s

abbrev TouchParams :=
  Σ V : Type u, Σ _ : DecidableEq V, Σ G : SimpleGraph V,
    Σ _ : DecidableRel G.Adj, Σ _ : Finset V, Σ _ : V, ℕ

abbrev SeedParams :=
  Σ V : Type u, Σ _ : DecidableEq V, Σ G : SimpleGraph V,
    Σ _ : DecidableRel G.Adj, Σ _ : Finset V, V

abbrev vertexSignature (P : Type (u + 1))
    (X : P → Type s) (Y : P → Type o) : Signature where
  Params := P
  State := X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := Y
  Anchor := Empty
  finiteAnchor := inferInstance

private theorem vertexSensitivity {P : Type (u + 1)} {X : P → Type s}
    {Y : P → Type o} (law : Realization (vertexSignature P X Y) → Prop)
    (actual bad : Realization (vertexSignature P X Y)) (reject : ¬ law bad) :
    Sensitivity ⟨vertexSignature P X Y, law⟩ actual := by
  constructor
  · intro i
    refine ⟨bad, ?_, ?_, reject⟩
    · exact fun j h => (h (Subsingleton.elim j i)).elim
    · funext e
      exact nomatch e
  · exact fun e => nomatch e

private abbrev Toy := ULift.{u} Bool
private abbrev left : Toy.{u} := ⟨false⟩
private abbrev right : Toy.{u} := ⟨true⟩
private abbrev toyGraph : SimpleGraph Toy.{u} := ⊥
local instance toyDec : DecidableRel toyGraph.{u}.Adj := fun _ _ => isFalse id

private theorem seed_touch : Touch toyGraph ({left} : Finset Toy.{u}) left 0 left 1 :=
  touch_zero_iff.mpr ⟨Finset.mem_singleton_self _, rfl, rfl⟩

private theorem false_touch : ¬ Touch toyGraph ({left} : Finset Toy.{u}) left 0 right 1 := by
  intro he
  have hr := (touch_zero_iff.mp he).2.1
  exact Bool.noConfusion (congrArg ULift.down hr)

private theorem vertex_touch_separates :
    (fun μ => Touch toyGraph ({left} : Finset Toy.{u}) left 0 left μ) ≠
      (fun μ => Touch toyGraph ({left} : Finset Toy.{u}) left 0 right μ) := by
  intro eq
  exact false_touch (congrFun eq 1 ▸ seed_touch)

private abbrev fullToy : Finset Toy.{u} := {left, right}

private abbrev topToy : SimpleGraph Toy.{u} := ⊤
local instance topToyDec : DecidableRel topToy.{u}.Adj := by
  intro v w
  change Decidable (v ≠ w)
  infer_instance
namespace TouchAtZero

abbrev signature : Signature.{u + 1, u, 0, 0, 0} :=
  vertexSignature SeedParams.{u} (fun p => p.1) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ p v μ => @Touch p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 0 v μ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena.{u + 1, u, 0, 0, 0} where
  signature := signature
  Law R := ∀ {V : Type u} [e : DecidableEq V] {G : SimpleGraph V} [i : DecidableRel G.Adj]
    {D : Finset V} {seed v : V} {μ : ℕ},
    R.readout () ⟨V, e, G, i, D, seed⟩ v μ ↔ v ∈ D ∧ v = seed ∧ μ = 1

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  exact (h (G := toyGraph) (D := {left}) (seed := left) (v := left) (μ := 1)).mpr
    ⟨Finset.mem_singleton_self _, rfl, rfl⟩

def family : Registration arena.{u} (type_of% @touch_zero_iff.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@touch_zero_iff, rejected, rejected_law⟩
  sensitivity :=
    vertexSensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    exact ⟨⟨Toy, inferInstance, toyGraph, toyDec, {left}, left⟩, left, right,
      vertex_touch_separates⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, u + 1, u, 0, 0, 0, 0}
    (@touch_zero_iff.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.TouchAtZero.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.TouchAtZero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v μ => @Touch p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 0 v μ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch
    definition := none
    coordinates := #[0, 2, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TouchAtZero

namespace TouchIsPositive

abbrev signature : Signature.{u + 1, u, 0, 0, 0} :=
  vertexSignature TouchParams.{u} (fun p => p.1) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ p v μ => @Touch p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2 v μ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena.{u + 1, u, 0, 0, 0} where
  signature := signature
  Law R := ∀ {V : Type u} [e : DecidableEq V] {G : SimpleGraph V} [i : DecidableRel G.Adj]
    {D : Finset V} {seed v : V} {t μ : ℕ},
    R.readout () ⟨V, e, G, i, D, seed, t⟩ v μ → v ∈ D ∧ 0 < μ

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  exact (by decide : ¬ 0 < (0 : ℕ))
    (h (G := toyGraph) (D := {left}) (seed := left) (v := left) (t := 0) (μ := 0) trivial).2

def family : Registration arena.{u} (type_of% @touch_retained_and_positive.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@touch_retained_and_positive, rejected, rejected_law⟩
  sensitivity :=
    vertexSensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    exact ⟨⟨Toy, inferInstance, toyGraph, toyDec, {left}, left, 0⟩, left, right,
      vertex_touch_separates⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, u + 1, u, 0, 0, 0, 0}
    (@touch_retained_and_positive.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.TouchIsPositive.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.TouchIsPositive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v μ => @Touch p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2 v μ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch
    definition := none
    coordinates := #[0, 2, 4, 5, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TouchIsPositive

namespace UniqueTouch

abbrev signature : Signature.{u + 1, u, 0, 0, 0} :=
  vertexSignature TouchParams.{u} (fun p => p.1) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ p v μ => @Touch p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2 v μ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena.{u + 1, u, 0, 0, 0} where
  signature := signature
  Law R := ∀ {V : Type u} [e : DecidableEq V] {G : SimpleGraph V} [i : DecidableRel G.Adj]
    {D : Finset V} {seed v : V} {t s μ : ℕ},
    R.readout () ⟨V, e, G, i, D, seed, s⟩ v μ → ∀ {ν : ℕ},
      Touch G D seed t v ν → s = t ∧ μ = ν

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have bad := (h (G := toyGraph) (s := 1) (μ := 1) trivial seed_touch).1
  omega

def family : Registration arena.{u} (type_of% @touch_unique.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@touch_unique, rejected, rejected_law⟩
  sensitivity :=
    vertexSensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    exact ⟨⟨Toy, inferInstance, toyGraph, toyDec, {left}, left, 0⟩, left, right,
      vertex_touch_separates⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, u + 1, u, 0, 0, 0, 0}
    (@touch_unique.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.UniqueTouch.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.UniqueTouch.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v μ => @Touch p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2 v μ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch
    definition := none
    coordinates := #[0, 2, 4, 5, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end UniqueTouch


namespace SendingNeighborhood

abbrev signature : Signature.{u + 1, u, 0, u, 0} :=
  vertexSignature TouchParams.{u} (fun p => p.1) (fun p => Finset p.1)

def actual : Realization signature :=
  realize signature (fun _ p v => @senders p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2 v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena.{u + 1, u, 0, u, 0} where
  signature := signature
  Law R := ∀ {V : Type u} [e : DecidableEq V] {G : SimpleGraph V} [i : DecidableRel G.Adj]
    {D : Finset V} {seed v : V} {t : ℕ} {w : V},
    w ∈ R.readout () ⟨V, e, G, i, D, seed, t⟩ v ↔
      w ∈ D ∧ G.Adj v w ∧ Born G D seed t w

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have born : Born topToy ({left} : Finset Toy.{u}) left 0 left :=
    touch_zero_iff.mpr ⟨Finset.mem_singleton_self _, rfl, rfl⟩
  have hm := (h (G := topToy) (D := {left}) (seed := left) (v := right) (t := 0) (w := left)).mpr
    ⟨Finset.mem_singleton_self _, by decide, born⟩
  simp [rejected, realize] at hm

def family : Registration arena.{u} (type_of% @mem_senders.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@mem_senders, rejected, rejected_law⟩
  sensitivity :=
    vertexSensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨⟨Toy, inferInstance, topToy, topToyDec, {left}, left, 0⟩, left, right, ?_⟩
    change senders topToy ({left} : Finset Toy.{u}) left 0 left ≠
      senders topToy ({left} : Finset Toy.{u}) left 0 right
    intro eq
    have born : Born topToy ({left} : Finset Toy.{u}) left 0 left :=
      touch_zero_iff.mpr ⟨Finset.mem_singleton_self _, rfl, rfl⟩
    have yes : left ∈ senders topToy ({left} : Finset Toy.{u}) left 0 right :=
      mem_senders.mpr ⟨Finset.mem_singleton_self _, by decide, born⟩
    rw [← eq] at yes
    exact SimpleGraph.irrefl topToy (mem_senders.mp yes).2.1

def audit : Contract.Registration.{_, _, _, 0, 0, 0, u + 1, u, 0, u, 0, 0}
    (@mem_senders.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.SendingNeighborhood.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.SendingNeighborhood.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => @senders p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch
    definition := none
    coordinates := #[0, 2, 4, 5, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SendingNeighborhood


namespace IntactState

abbrev signature : Signature.{u + 1, 0, 0, u, 0} :=
  vertexSignature SeedParams.{u} (fun _ => ℕ) (fun p => p.1 → Prop)

def actual : Realization signature :=
  realize signature (fun _ p t => @Intact p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena.{u + 1, 0, 0, u, 0} where
  signature := signature
  Law R := ∀ {V : Type u} [e : DecidableEq V] {G : SimpleGraph V} [i : DecidableRel G.Adj]
    {D : Finset V} {seed v : V} {t : ℕ},
    R.readout () ⟨V, e, G, i, D, seed⟩ t v ↔ ∀ s ≤ t, ∀ μ, ¬ Touch G D seed s v μ

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  exact (h (G := toyGraph) (D := {left}) (seed := left) (v := left) (t := 0)).mp
    trivial 0 (by decide) 1 seed_touch

def family : Registration arena.{u} (type_of% @intact_iff_no_touch.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@intact_iff_no_touch, rejected, rejected_law⟩
  sensitivity :=
    vertexSensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨⟨Toy, inferInstance, topToy, topToyDec, fullToy, left⟩, 0, 1, ?_⟩
    change Intact topToy (fullToy : Finset Toy.{u}) left 0 ≠
      Intact topToy fullToy left 1
    intro eq
    have h₀ : Intact topToy (fullToy : Finset Toy.{u}) left 0 right := by
      unfold Intact
      decide
    have h₁ : ¬ Intact topToy (fullToy : Finset Toy.{u}) left 1 right := by
      unfold Intact
      decide
    exact h₁ (congrFun eq right ▸ h₀)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, u + 1, 0, 0, u, 0, 0}
    (@intact_iff_no_touch.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.IntactState.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.IntactState.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p t => @Intact p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch
    definition := none
    coordinates := #[0, 2, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end IntactState

namespace StrictHorizon

abbrev signature : Signature.{u + 1, 0, 0, u, 0} :=
  vertexSignature SeedParams.{u} (fun _ => ℕ) (fun p => p.1 → Prop)

def actual : Realization signature :=
  realize signature (fun _ p t => @Born p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena.{u + 1, 0, 0, u, 0} where
  signature := signature
  Law R := ∀ {V : Type u} [e : DecidableEq V] {G : SimpleGraph V} [i : DecidableRel G.Adj]
    {D E : Finset V} {seed : V} (h : V → ℕ) (_sub : D ⊆ E) (_seed_mem : seed ∈ D)
    (_edge_step : ∀ ⦃v w⦄, G.Adj v w → h v ≤ h w + 1)
    (_wall : ∀ ⦃v⦄, v ∈ E → v ∉ D → (∃ w ∈ D, G.Adj v w) →
      ∀ t < h v, ¬ Born G E seed t v) (t : ℕ),
    (∀ v ∈ D, t < h v → ∀ μ, 0 < μ →
      (Touch G D seed t v μ ↔ Touch G E seed t v μ)) ∧
    (∀ v ∈ E, v ∉ D → t < h v → ¬ R.readout () ⟨V, e, G, i, E, seed⟩ t v)

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have sub : ({left} : Finset Toy.{u}) ⊆ fullToy := by
    intro v hv
    rcases Finset.mem_singleton.mp hv with rfl
    exact Finset.mem_insert_self _ _
  have hh := h (G := toyGraph) (seed := left) (fun _ => 1) sub (Finset.mem_singleton_self _)
    (by intro v w noEdge; exact noEdge.elim)
    (by intro v out disj near; obtain ⟨w, hw, noEdge⟩ := near; exact noEdge.elim) 0
  exact hh.2 right (by decide) (by decide) (by decide) trivial

def family : Registration arena.{u} (type_of% @strict_horizon.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@strict_horizon, rejected, rejected_law⟩
  sensitivity :=
    vertexSensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨⟨Toy, inferInstance, toyGraph, toyDec, fullToy, left⟩, 0, 1, ?_⟩
    change Born toyGraph (fullToy : Finset Toy.{u}) left 0 ≠
      Born toyGraph fullToy left 1
    intro eq
    have first : Born toyGraph (fullToy : Finset Toy.{u}) left 0 left :=
      touch_zero_iff.mpr ⟨Finset.mem_insert_self _ _, rfl, rfl⟩
    have later : Born toyGraph (fullToy : Finset Toy.{u}) left 1 left :=
      congrFun eq left ▸ first
    have absurd := (touch_unique first later).1
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, u + 1, 0, 0, u, 0, 0}
    (@strict_horizon.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.StrictHorizon.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch.StrictHorizon.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p t => @Born p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch
    definition := none
    coordinates := #[0, 2, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end StrictHorizon

end

end Reg.D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch
