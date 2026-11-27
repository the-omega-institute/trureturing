/- GID: D5/S3/Combinatorics/Graph/VertexDeletion/TailComponents
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/VertexDeletion/TailComponents
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual tail runs and induced survivor scores for exact vertex cuts. -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-! Actual tail runs and induced survivor scores for exact vertex cuts. -/

set_option autoImplicit false
set_option linter.style.openClassical false

namespace Ugurlu33528

open SimpleGraph

/-- A walk with projected steps of size zero or one cannot cross an omitted position. -/
private theorem reachable_lt_iff_of_omitted_position {V : Type*} {G : SimpleGraph V}
    (pos : V → ℕ) (cut : ℕ) (omitted : ∀ v, pos v ≠ cut)
    (unitStep : ∀ u v, G.Adj u v →
      pos u = pos v ∨ pos u + 1 = pos v ∨ pos v + 1 = pos u)
    {x y : V} (walk : G.Reachable x y) : pos x < cut ↔ pos y < cut := by
  have edgeSameSide (u v : V) (edge : G.Adj u v) : pos u < cut ↔ pos v < cut := by
    have hu := omitted u
    have hv := omitted v
    rcases unitStep u v edge with h | h | h <;> omega
  have closure := (G.reachable_iff_reflTransGen x y).mp walk
  clear walk
  induction closure with
  | refl => rfl
  | tail _ edge ih => exact ih.trans (edgeSameSide _ _ edge)

/-- A spine vertex or a leaf indexed by its hub and its label at that hub. -/
abbrev Vertex (p t b k : ℕ) := Fin (p + t) ⊕ (Fin b × Fin k)

private def hostAdj {p t b k : ℕ} (hub : Fin b → Fin p) :
    Vertex p t b k → Vertex p t b k → Prop
  | .inl i, .inl j => (pathGraph (p + t)).Adj i j
  | .inl i, .inr leaf => i = (hub leaf.1).castAdd t
  | .inr leaf, .inl i => i = (hub leaf.1).castAdd t
  | .inr _, .inr _ => False

/-- The whole spine is a path. Each leaf meets only its specified hub. -/
def host {p t b k : ℕ} (hub : Fin b → Fin p) : SimpleGraph (Vertex p t b k) where
  Adj := hostAdj hub
  symm.symm u v edge := by
    cases u <;> cases v
    · exact edge.symm
    · exact edge
    · exact edge
    · exact edge
  loopless.irrefl u edge := by
    cases u
    · exact (pathGraph (p + t)).loopless.irrefl _ edge
    · exact edge

def position {p t b k : ℕ} (hub : Fin b → Fin p) : Vertex p t b k → ℕ
  | .inl i => i.val
  | .inr leaf => (hub leaf.1).val

def tailVertex {p t b k : ℕ} (i : Fin t) : Vertex p t b k :=
  .inl (Fin.natAdd p i)

def survivors {V : Type*} [DecidableEq V] (D : Finset V) : Set V :=
  {v | v ∉ D}

def survivorGraph {V : Type*} [DecidableEq V] (G : SimpleGraph V) (D : Finset V) :
    SimpleGraph (survivors D) :=
  G.induce (survivors D)

section Host

variable {p t b k : ℕ} (hub : Fin b → Fin p) (D : Finset (Vertex p t b k))

theorem host_adj_position (u v : Vertex p t b k) (edge : (host hub).Adj u v) :
    position hub u = position hub v ∨
      position hub u + 1 = position hub v ∨ position hub v + 1 = position hub u := by
  cases u with
  | inl i =>
    cases v with
    | inl j => exact Or.inr (pathGraph_adj.mp edge)
    | inr leaf =>
      change i = (hub leaf.1).castAdd t at edge
      subst i
      exact Or.inl rfl
  | inr leaf =>
    cases v with
    | inl i =>
      change i = (hub leaf.1).castAdd t at edge
      subst i
      exact Or.inl rfl
    | inr _ => exact False.elim edge

/-- A deleted tail spine vertex has no surviving vertex in its projection fiber. -/
private theorem omitted_tail_position {c : Fin t}
    (hc : tailVertex (p := p) (b := b) (k := k) c ∈ D) (v : survivors D) :
    position hub v.val ≠ p + c.val := by
  intro hpos
  obtain ⟨v, hv⟩ := v
  cases v with
  | inl i =>
    exact hv (show Sum.inl i ∈ D from
      (congrArg Sum.inl (Fin.ext hpos) : Sum.inl i = tailVertex c).symm ▸ hc)
  | inr leaf =>
    have hlt := (hub leaf.1).isLt
    change (hub leaf.1).val = p + c.val at hpos
    omega

def survivingTailVertex (i : Fin t) (hi : tailVertex (p := p) (b := b) (k := k) i ∉ D) :
    survivors D := ⟨tailVertex i, hi⟩

/-- Applies the cut invariant to reachability in the actual induced survivor graph. -/
private theorem tail_cut {x c y : Fin t} (hx : tailVertex (p := p) (b := b) (k := k) x ∉ D)
    (hc : tailVertex c ∈ D) (hy : tailVertex y ∉ D)
    (hxc : x.val < c.val) (hcy : c.val < y.val) :
    ¬ (survivorGraph (host hub) D).Reachable
      (survivingTailVertex D x hx) (survivingTailVertex D y hy) := by
  intro walk
  have sameSide := reachable_lt_iff_of_omitted_position
    (G := survivorGraph (host hub) D) (fun v => position hub v.val) (p + c.val)
    (omitted_tail_position hub D hc)
    (fun u v edge => host_adj_position hub u.val v.val (induce_adj.mp edge)) walk
  change (p + x.val < p + c.val ↔ p + y.val < p + c.val) at sameSide
  exact (Nat.not_lt_of_ge (by omega)) (sameSide.mp (by omega))

end Host

section TailRuns

variable {p t b k : ℕ} (hub : Fin b → Fin p) (D : Finset (Vertex p t b k))

theorem tail_interval_reachable {x y : Fin t}
    (hx : tailVertex (p := p) (b := b) (k := k) x ∉ D) (hy : tailVertex y ∉ D)
    (hxy : x.val ≤ y.val)
    (allSurvive : ∀ z : Fin t, x.val ≤ z.val → z.val ≤ y.val → tailVertex z ∉ D) :
    (survivorGraph (host hub) D).Reachable
      (survivingTailVertex D x hx) (survivingTailVertex D y hy) := by
  have reach (n : ℕ) (lower : x.val ≤ n) (upper : n ≤ y.val) :
      (survivorGraph (host hub) D).Reachable (survivingTailVertex D x hx)
        (survivingTailVertex D ⟨n, lt_of_le_of_lt upper y.isLt⟩
          (allSurvive _ lower upper)) := by
    induction n, lower using Nat.le_induction with
    | base => exact SimpleGraph.Reachable.rfl
    | succ n hn ih =>
      apply (ih (Nat.le_of_succ_le upper)).trans
      apply SimpleGraph.Adj.reachable
      apply induce_adj.mpr
      apply pathGraph_adj.mpr
      exact Or.inl rfl
  exact reach y.val hxy le_rfl

/-- Two ordered surviving tail vertices are in the same component exactly when the
whole tail interval between them survives. Both components are in the induced host. -/
theorem tail_component_eq_iff {x y : Fin t}
    (hx : tailVertex (p := p) (b := b) (k := k) x ∉ D) (hy : tailVertex y ∉ D)
    (hxy : x.val ≤ y.val) :
    (survivorGraph (host hub) D).connectedComponentMk (survivingTailVertex D x hx) =
      (survivorGraph (host hub) D).connectedComponentMk (survivingTailVertex D y hy) ↔
      ∀ z : Fin t, x.val ≤ z.val → z.val ≤ y.val → tailVertex z ∉ D := by
  rw [SimpleGraph.ConnectedComponent.eq]
  refine ⟨fun walk z hl hr deleted => ?_, tail_interval_reachable hub D hx hy hxy⟩
  have hzx : z.val ≠ x.val := fun h => hx (Fin.ext h ▸ deleted)
  have hzy : z.val ≠ y.val := fun h => hy (Fin.ext h ▸ deleted)
  exact tail_cut hub D hx deleted hy (by omega) (by omega) walk

/-- A nonempty maximal interval of surviving tail vertices. -/
@[ext] structure TailRun (D : Finset (Vertex p t b k)) where
  first : Fin t
  last : Fin t
  ordered : first.val ≤ last.val
  survives : ∀ z : Fin t, first.val ≤ z.val → z.val ≤ last.val → tailVertex z ∉ D
  leftMax : ∀ z : Fin t, z.val + 1 = first.val → tailVertex z ∈ D
  rightMax : ∀ z : Fin t, last.val + 1 = z.val → tailVertex z ∈ D

def TailRun.component (r : TailRun D) : (survivorGraph (host hub) D).ConnectedComponent :=
  (survivorGraph (host hub) D).connectedComponentMk
    (survivingTailVertex D r.first (r.survives r.first le_rfl r.ordered))

theorem TailRun.component_eq (r : TailRun D) (z : Fin t)
    (hl : r.first.val ≤ z.val) (hr : z.val ≤ r.last.val) :
    r.component hub =
      (survivorGraph (host hub) D).connectedComponentMk
        (survivingTailVertex D z (r.survives z hl hr)) := by
  exact (tail_component_eq_iff hub D _ _ hl).2
    (fun w hw₁ hw₂ => r.survives w hw₁ (hw₂.trans hr))

private theorem TailRun.eq_of_first_eq (r s : TailRun D) (hfirst : r.first = s.first) : r = s := by
  apply TailRun.ext hfirst
  apply Fin.ext
  have cannot_extend (r s : TailRun D) (h : r.first = s.first) (hlt : r.last.val < s.last.val) :
      False := by
    let z : Fin t := ⟨r.last.val + 1, lt_of_le_of_lt hlt s.last.isLt⟩
    have hleft := r.ordered
    rw [h] at hleft
    exact s.survives z (by dsimp [z]; omega) hlt (r.rightMax z rfl)
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · exact cannot_extend r s hfirst h
  · exact cannot_extend s r hfirst.symm h

private theorem TailRun.last_lt_first (r s : TailRun D) (hlt : r.first.val < s.first.val) :
    r.last.val < s.first.val := by
  by_contra! h
  let z : Fin t := ⟨s.first.val - 1, by have := s.first.isLt; omega⟩
  have hz : z.val + 1 = s.first.val := by dsimp [z]; omega
  exact r.survives z (by omega) (by omega) (s.leftMax z hz)

/-- Distinct positive tail runs give distinct components of the induced host. -/
theorem tail_run_component_injective : Function.Injective (TailRun.component hub (D := D)) := by
  intro r s sameComponent
  have cannot_join (r s : TailRun D) (hlt : r.first.val < s.first.val) :
      r.component hub ≠ s.component hub := by
    have gap := r.last_lt_first D s hlt
    let c : Fin t := ⟨r.last.val + 1, lt_of_le_of_lt gap s.first.isLt⟩
    have deleted := r.rightMax c rfl
    have hc_lt : c.val < s.first.val := by
      have hne : c.val ≠ s.first.val := fun h =>
        s.survives s.first le_rfl s.ordered (Fin.ext h ▸ deleted)
      dsimp [c] at hne ⊢
      omega
    intro h
    have connected := SimpleGraph.ConnectedComponent.exact h
    exact tail_cut hub D (r.survives r.first le_rfl r.ordered) deleted
      (s.survives s.first le_rfl s.ordered) (by have := r.ordered; dsimp [c]; omega)
      hc_lt connected
  rcases lt_trichotomy r.first.val s.first.val with h | h | h
  · exact (cannot_join r s h sameComponent).elim
  · exact r.eq_of_first_eq D s (Fin.ext h)
  · exact (cannot_join s r h sameComponent.symm).elim

end TailRuns

/-- Alternating hubs on the prefix positions 1, 3, …, 2b − 1 (zero-based). -/
def uniformHub (b : ℕ) (i : Fin b) : Fin (2 * b) := ⟨2 * i.val + 1, by omega⟩

theorem uniform_hubs_independent (b : ℕ) :
    Function.Injective (uniformHub b) ∧
      ∀ i j, ¬ (pathGraph (2 * b)).Adj (uniformHub b i) (uniformHub b j) := by
  constructor
  · intro i j he
    have hv := congrArg Fin.val he
    change 2 * i.val + 1 = 2 * j.val + 1 at hv
    exact Fin.ext (by omega)
  · intro i j edge
    rcases pathGraph_adj.mp edge with h | h <;> dsimp [uniformHub] at h <;> omega

/-- Taking q as the balanced part size leaves (b+1)q vertices after deletion.
The intact prefix and its leaves account for b(k+2) original vertices. -/
def uniformTailLength (b k q : ℕ) : ℕ := (b + 1) * q + b - b * (k + 2)

abbrev UniformVertex (b k q : ℕ) := Vertex (2 * b) (uniformTailLength b k q) b k

def uniformHost (b k q : ℕ) : SimpleGraph (UniformVertex b k q) := host (uniformHub b)

theorem uniform_survivor_card {b k q : ℕ} (hq : 2 * b * (k + 2) ≤ q)
    (D : Finset (UniformVertex b k q)) (hD : D.card = b) :
    (Dᶜ).card = (b + 1) * q := by
  have hprefix : b * (k + 2) = 2 * b + b * k := by
    simp only [Nat.mul_add, Nat.mul_comm b 2, Nat.add_comm]
  have hbound : b * (k + 2) ≤ (b + 1) * q + b := by
    have h₁ : b * (k + 2) ≤ q := by
      rw [Nat.mul_assoc] at hq
      omega
    rw [Nat.add_mul, Nat.one_mul]
    omega
  rw [Finset.card_compl, hD]
  change Fintype.card (Fin (2 * b + uniformTailLength b k q) ⊕ (Fin b × Fin k)) - b =
    (b + 1) * q
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  unfold uniformTailLength
  omega

section ComponentScores

variable {V : Type*} [DecidableEq V] [Fintype V]

instance instFintypeSurvivors (D : Finset V) : Fintype (survivors D) :=
  Fintype.ofFinset (Dᶜ) (by simp [survivors])

instance instDecidableSurvivorAdj (G : SimpleGraph V) (D : Finset V) [DecidableRel G.Adj] :
    DecidableRel (survivorGraph G D).Adj :=
  fun x y => inferInstanceAs (Decidable (G.Adj x.val y.val))

/-- Component sizes counted directly on the induced graph, with multiplicities. -/
def componentSizes (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) : Multiset ℕ :=
  (Finset.univ : Finset (survivorGraph G D).ConnectedComponent).val.map
    (fun C => C.supp.toFinset.card)

def ncDamage (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) : ℕ :=
  (componentSizes G D).card - 1

def pcDamage (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) : ℕ :=
  (Fintype.card V).choose 2 - ((componentSizes G D).map (fun c => c.choose 2)).sum

def lccDamage (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) : ℕ :=
  Fintype.card V - (componentSizes G D).sup

def damageMaximum (score : Finset V → ℕ) (b : ℕ) : ℕ :=
  ((Finset.univ : Finset V).powersetCard b).sup score

end ComponentScores
instance instDecidableRelVertexAdjHost {p t b k : ℕ} (hub : Fin b → Fin p) : DecidableRel (@host p t b k hub).Adj
  | .inl _, .inl _ => inferInstanceAs (Decidable ((pathGraph (p + t)).Adj _ _))
  | .inl _, .inr _ => inferInstanceAs (Decidable (_ = (_ : Fin (p + t))))
  | .inr _, .inl _ => inferInstanceAs (Decidable (_ = (_ : Fin (p + t))))
  | .inr _, .inr _ => inferInstanceAs (Decidable False)
end Ugurlu33528

namespace Ugurlu33528

open SimpleGraph
open scoped BigOperators Classical

section TailComponentMass

variable {p t b k : ℕ} (hub : Fin b → Fin p) (D : Finset (Vertex p t b k))

def deletedTailIndices : Finset (Fin t) :=
  Finset.univ.filter fun i => tailVertex i ∈ D

def survivingTailVertices : Finset (survivors D) :=
  Finset.univ.filter fun v => p ≤ position hub v.val

noncomputable def positiveTailComponents : Finset (survivorGraph (host hub) D).ConnectedComponent :=
  (survivingTailVertices hub D).image (survivorGraph (host hub) D).connectedComponentMk

private noncomputable def tailMass (C : (survivorGraph (host hub) D).ConnectedComponent) : ℕ :=
  ((survivingTailVertices hub D).filter
    fun v => (survivorGraph (host hub) D).connectedComponentMk v = C).card

theorem mem_deletedTailIndices (i : Fin t) :
    i ∈ deletedTailIndices D ↔ tailVertex i ∈ D := by
  simp [deletedTailIndices]

theorem survivingTailVertex_mem (i : Fin t) (hi : tailVertex i ∉ D) :
    survivingTailVertex D i hi ∈ survivingTailVertices hub D := by
  rw [survivingTailVertices, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, Nat.le_add_right p i.val⟩

theorem exists_survivingTailVertex {v : survivors D}
    (hv : v ∈ survivingTailVertices hub D) :
    ∃ (i : Fin t) (hi : tailVertex i ∉ D), survivingTailVertex D i hi = v := by
  have hpos := (Finset.mem_filter.mp hv).2
  obtain ⟨v, hSurvives⟩ := v
  cases v with
  | inl j =>
    change p ≤ j.val at hpos
    let i : Fin t := ⟨j.val - p, by have := j.isLt; omega⟩
    have h : tailVertex (b := b) (k := k) i = Sum.inl j := by
      apply congrArg Sum.inl
      apply Fin.ext
      change p + (j.val - p) = j.val
      omega
    exact ⟨i, fun hdel => hSurvives (h ▸ hdel), Subtype.ext h⟩
  | inr leaf =>
    change p ≤ (hub leaf.1).val at hpos
    exact ((hub leaf.1).isLt.not_ge hpos).elim

theorem survivingTailVertices_card :
    (survivingTailVertices hub D).card = t - (deletedTailIndices D).card := by
  let f : ↥((deletedTailIndices D)ᶜ) → ↥(survivingTailVertices hub D) := fun i =>
    have hi : tailVertex i.val ∉ D := fun h => (Finset.mem_compl.mp i.property)
      ((mem_deletedTailIndices D i.val).mpr h)
    ⟨survivingTailVertex D i.val hi, survivingTailVertex_mem hub D i.val hi⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      have hval := congrArg (fun v : ↥(survivingTailVertices hub D) =>
        position hub v.val.val) h
      change p + i.val.val = p + j.val.val at hval
      exact Subtype.ext (Fin.ext (Nat.add_left_cancel hval))
    · intro v
      obtain ⟨i, hi, he⟩ := exists_survivingTailVertex hub D v.property
      exact ⟨⟨i, Finset.mem_compl.mpr (fun h => hi ((mem_deletedTailIndices D i).mp h))⟩,
        Subtype.ext he⟩
  have h := Fintype.card_congr (Equiv.ofBijective f hf)
  rw [Fintype.card_coe, Fintype.card_coe, Finset.card_compl, Fintype.card_fin] at h
  exact h.symm

/-- The extreme tail indices of a positive-tail component give a maximal surviving run. -/
theorem positiveTailComponent_has_run {C : (survivorGraph (host hub) D).ConnectedComponent}
    (hC : C ∈ positiveTailComponents hub D) :
    ∃ r : TailRun D, r.component hub = C := by
  classical
  let G := survivorGraph (host hub) D
  let indices : Finset (Fin t) := Finset.univ.filter fun i =>
    ∃ hi : tailVertex i ∉ D, G.connectedComponentMk (survivingTailVertex D i hi) = C
  have memIndices (i : Fin t) : i ∈ indices ↔
      ∃ hi : tailVertex i ∉ D, G.connectedComponentMk (survivingTailVertex D i hi) = C := by
    simp [indices]
  unfold positiveTailComponents at hC
  obtain ⟨v, hv, hvc⟩ := Finset.mem_image.mp hC
  obtain ⟨i, hi, rfl⟩ := exists_survivingTailVertex hub D hv
  have hNonempty : indices.Nonempty := ⟨i, (memIndices i).mpr ⟨hi, hvc⟩⟩
  let first := indices.min' hNonempty
  let last := indices.max' hNonempty
  obtain ⟨hFirst, hFirstC⟩ := (memIndices first).mp (indices.min'_mem hNonempty)
  obtain ⟨hLast, hLastC⟩ := (memIndices last).mp (indices.max'_mem hNonempty)
  have ordered : first.val ≤ last.val := indices.min'_le _ (indices.max'_mem hNonempty)
  have interval := (tail_component_eq_iff hub D hFirst hLast ordered).mp
    (hFirstC.trans hLastC.symm)
  have adjacent {x y : Fin t} (hx : tailVertex x ∉ D) (hy : tailVertex y ∉ D)
      (hxy : x.val + 1 = y.val) :
      G.connectedComponentMk (survivingTailVertex D x hx) =
        G.connectedComponentMk (survivingTailVertex D y hy) := by
    apply SimpleGraph.ConnectedComponent.eq.mpr
    apply SimpleGraph.Adj.reachable
    apply induce_adj.mpr
    apply pathGraph_adj.mpr
    left
    change p + x.val + 1 = p + y.val
    omega
  have leftMax (z : Fin t) (hz : z.val + 1 = first.val) : tailVertex z ∈ D := by
    by_contra deleted
    have hzC := (adjacent deleted hFirst hz).trans hFirstC
    have h := indices.min'_le z ((memIndices z).mpr ⟨deleted, hzC⟩)
    change first.val ≤ z.val at h
    omega
  have rightMax (z : Fin t) (hz : last.val + 1 = z.val) : tailVertex z ∈ D := by
    by_contra deleted
    have hzC := (adjacent hLast deleted hz).symm.trans hLastC
    have h := indices.le_max' z ((memIndices z).mpr ⟨deleted, hzC⟩)
    change z.val ≤ last.val at h
    omega
  exact ⟨⟨first, last, ordered, interval, leftMax, rightMax⟩, hFirstC⟩

/-- Index zero uses the sentinel. Every other run uses its deleted predecessor. -/
def TailRun.predecessorOrFirst (r : TailRun D) : Option ↥(deletedTailIndices D) :=
  if h : r.first.val = 0 then none
  else
    let i : Fin t := ⟨r.first.val - 1, by have := r.first.isLt; omega⟩
    some ⟨i, (mem_deletedTailIndices D i).mpr (r.leftMax i (by dsimp [i]; omega))⟩

theorem TailRun.predecessorOrFirst_injective :
    Function.Injective (TailRun.predecessorOrFirst D) := by
  have decode (r : TailRun D) :
      (r.predecessorOrFirst D).elim 0 (fun i => i.val.val + 1) = r.first.val := by
    unfold TailRun.predecessorOrFirst
    split
    · simp_all
    · change r.first.val - 1 + 1 = r.first.val
      omega
  intro r s h
  apply r.eq_of_first_eq D s
  apply Fin.ext
  rw [← decode r, ← decode s, h]

private theorem positiveTailComponents_card_le :
    (positiveTailComponents hub D).card ≤ (deletedTailIndices D).card + 1 := by
  classical
  let J := positiveTailComponents hub D
  let run (C : ↥J) : TailRun D :=
    (positiveTailComponent_has_run hub D C.property).choose
  have represents (C : ↥J) : (run C).component hub = C.val :=
    (positiveTailComponent_has_run hub D C.property).choose_spec
  let f : ↥J → Option ↥(deletedTailIndices D) := fun C => (run C).predecessorOrFirst D
  have hf : Function.Injective f := by
    intro C C' h
    have sameRun := TailRun.predecessorOrFirst_injective D h
    exact Subtype.ext ((represents C).symm.trans
      ((congrArg (TailRun.component hub D) sameRun).trans (represents C')))
  simpa only [Fintype.card_coe, Fintype.card_option] using Fintype.card_le_of_injective f hf

private theorem sum_tailMass :
    (∑ C ∈ positiveTailComponents hub D, tailMass hub D C) =
      t - (deletedTailIndices D).card := by
  calc
    _ = (survivingTailVertices hub D).card :=
      (Finset.card_eq_sum_card_image (survivorGraph (host hub) D).connectedComponentMk _).symm
    _ = _ := survivingTailVertices_card hub D

end TailComponentMass

theorem uniform_tail_component_count_and_mass {b k q : ℕ}
    (_hb : 2 ≤ b) (_hk : 1 ≤ k) (_hq : 2 * b * (k + 2) ≤ q)
    (D : Finset (UniformVertex b k q)) (_hD : D.card = b) :
    let t := uniformTailLength b k q
    let G := survivorGraph (uniformHost b k q) D
    let I := (Finset.univ : Finset (Fin t)).filter (fun i => tailVertex i ∈ D)
    let A := (Finset.univ : Finset (survivors D)).filter
      (fun v => 2 * b ≤ position (uniformHub b) v.val)
    let J := A.image G.connectedComponentMk
    let w := fun C => (A.filter (fun v => G.connectedComponentMk v = C)).card
    J.card ≤ I.card + 1 ∧
      (∑ C ∈ J, w C) = t - I.card ∧
      ∀ C ∈ J, w C ≤ C.supp.toFinset.card := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact positiveTailComponents_card_le (uniformHub b) D
  · exact sum_tailMass (uniformHub b) D
  · intro C _
    apply Finset.card_le_card
    intro v hv
    exact Set.mem_toFinset.mpr
      ((ConnectedComponent.mem_supp_iff C v).mpr (Finset.mem_filter.mp hv).2)

end Ugurlu33528

namespace Ugurlu33528

open SimpleGraph
open scoped BigOperators Classical

private theorem uniform_tail_mass_lower {b k q : ℕ}
    (D : Finset (UniformVertex b k q)) (hD : D.card = b) :
    (b + 1) * q - b * (k + 2) ≤ uniformTailLength b k q - (deletedTailIndices D).card := by
  have hDeleted : (deletedTailIndices D).card ≤ D.card := by
    apply Finset.card_le_card_of_injOn
      (tailVertex (p := 2 * b) (b := b) (k := k))
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i _ j _ hij
      exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val (Sum.inl.inj hij)))
  calc
    _ = uniformTailLength b k q - b := by
      unfold uniformTailLength
      rw [Nat.sub_right_comm, Nat.add_sub_cancel]
    _ ≤ _ := Nat.sub_le_sub_left (hDeleted.trans_eq hD) _

set_option maxHeartbeats 800000 in
/-- With at most b tail-bearing components, an exact cut has an actual component
larger than q and its actual component square sum is strictly above the balanced value. -/
private theorem uniform_fewer_tail_components_strict_optimizer_bounds {b k q : ℕ}
    (hb : 2 ≤ b) (hk : 1 ≤ k) (hq : 2 * b * (k + 2) ≤ q)
    (D : Finset (UniformVertex b k q)) (hD : D.card = b)
    (hJ : (positiveTailComponents (uniformHub b) D).card ≤ b) :
    let G := survivorGraph (uniformHost b k q) D
    (∃ C : G.ConnectedComponent, q < C.supp.toFinset.card) ∧
      (b + 1) * q ^ 2 < ∑ C : G.ConnectedComponent, C.supp.toFinset.card ^ 2 := by
  dsimp only
  let G := survivorGraph (uniformHost b k q) D
  let J : Finset G.ConnectedComponent := positiveTailComponents (uniformHub b) D
  let w : G.ConnectedComponent → ℕ := tailMass (uniformHub b) D
  let c (C : G.ConnectedComponent) := C.supp.toFinset.card
  let U := ∑ C ∈ J, w C
  change (∃ C : G.ConnectedComponent, q < c C) ∧
    (b + 1) * q ^ 2 < ∑ C : G.ConnectedComponent, c C ^ 2
  have hTail : U = uniformTailLength b k q - (deletedTailIndices D).card ∧
      ∀ C ∈ J, w C ≤ c C :=
    (uniform_tail_component_count_and_mass hb hk hq D hD).2
  have hMass : (b + 1) * q - b * (k + 2) ≤ U :=
    hTail.1.symm ▸ uniform_tail_mass_lower D hD
  have hqTwice : 2 * (b * (k + 2)) ≤ q := by simpa only [Nat.mul_assoc] using hq
  have hPrefixPos : 0 < b * (k + 2) := Nat.mul_pos (by omega) (by omega)
  have hqPos : 0 < q := by omega
  have hDouble : 2 * (b * q) + q ≤ 2 * U := by
    rw [Nat.add_mul, Nat.one_mul] at hMass
    omega
  constructor
  · by_contra! hAll
    have hSum : U ≤ J.card * q := by
      calc
        U ≤ ∑ C ∈ J, q := Finset.sum_le_sum fun C hC => (hTail.2 C hC).trans (hAll C)
        _ = J.card * q := by simp
    have hUpper := hSum.trans (Nat.mul_le_mul_right q hJ)
    omega
  · have hScaled : 4 * (b * ((b + 1) * q ^ 2)) < 4 * (U ^ 2) := by
      calc
        _ < (2 * (b * q) + q) ^ 2 := by
          rw [show (2 * (b * q) + q) ^ 2 = 4 * (b * ((b + 1) * q ^ 2)) + q ^ 2 by ring]
          exact Nat.lt_add_of_pos_right (Nat.pow_pos hqPos)
        _ ≤ (2 * U) ^ 2 := Nat.pow_le_pow_left hDouble 2
        _ = _ := by ring
    have hStrict := Nat.lt_of_mul_lt_mul_left hScaled
    have hSquares : U ^ 2 ≤ b * (∑ C : G.ConnectedComponent, c C ^ 2) := by
      calc
        U ^ 2 ≤ J.card * ∑ C ∈ J, w C ^ 2 := sq_sum_le_card_mul_sum_sq
        _ ≤ b * ∑ C ∈ J, w C ^ 2 := Nat.mul_le_mul_right _ hJ
        _ ≤ b * ∑ C ∈ J, c C ^ 2 :=
          Nat.mul_le_mul_left b (Finset.sum_le_sum fun C hC =>
            Nat.pow_le_pow_left (hTail.2 C hC) 2)
        _ ≤ b * ∑ C : G.ConnectedComponent, c C ^ 2 :=
          Nat.mul_le_mul_left b (Finset.sum_le_sum_of_subset
            (f := fun C : G.ConnectedComponent => c C ^ 2) (Finset.subset_univ J))
    exact Nat.lt_of_mul_lt_mul_left (hStrict.trans_le hSquares)

end Ugurlu33528

namespace Ugurlu33528

open SimpleGraph
open scoped BigOperators Classical

/-- The actual connected component supports partition the surviving vertices. -/
theorem sum_component_card {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ C : G.ConnectedComponent, C.supp.toFinset.card) = Fintype.card V := by
  have hImage : Finset.univ.image G.connectedComponentMk = Finset.univ :=
    Finset.image_univ_of_surjective Quot.mk_surjective
  calc
    _ = ∑ C : G.ConnectedComponent,
        (Finset.univ.filter fun v => G.connectedComponentMk v = C).card := by
      congr 1
      funext C
      congr 1
      ext v
      simp only [Set.mem_toFinset, ConnectedComponent.mem_supp_iff,
        Finset.mem_filter, Finset.mem_univ, true_and]
    _ = Fintype.card V := by
      rw [← hImage, ← Finset.card_eq_sum_card_image, Finset.card_univ]

theorem twice_choose_two_add (n : ℕ) : 2 * n.choose 2 + n = n ^ 2 := by
  rw [Nat.choose_two_right, Nat.mul_comm 2, Nat.div_mul_cancel (Nat.even_mul_pred_self n).two_dvd,
    Nat.mul_sub_left_distrib, Nat.mul_one, pow_two]
  exact Nat.sub_add_cancel (Nat.le_mul_self n)

set_option maxHeartbeats 800000 in
/-- A cut with at most b tail-bearing components has strictly smaller PC and LCC
damage than the scores of the profile with b+1 parts of size q. -/
theorem uniform_fewer_tail_components_strict_score_comparisons {b k q : ℕ}
    (hb : 2 ≤ b) (hk : 1 ≤ k) (hq : 2 * b * (k + 2) ≤ q)
    (D : Finset (UniformVertex b k q)) (hD : D.card = b)
    (hJ : (positiveTailComponents (uniformHub b) D).card ≤ b) :
    let G := survivorGraph (uniformHost b k q) D
    let n := Fintype.card (UniformVertex b k q)
    (b + 1) * q.choose 2 < (∑ C : G.ConnectedComponent, C.supp.toFinset.card.choose 2) ∧
      pcDamage (uniformHost b k q) D < n.choose 2 - (b + 1) * q.choose 2 ∧
      lccDamage (uniformHost b k q) D < n - q := by
  dsimp only
  let G := survivorGraph (uniformHost b k q) D
  let c (C : G.ConnectedComponent) := C.supp.toFinset.card
  let n := Fintype.card (UniformVertex b k q)
  let S := (b + 1) * q
  let pairs := ∑ C : G.ConnectedComponent, (c C).choose 2
  let balancedPairs := (b + 1) * q.choose 2
  change balancedPairs < pairs ∧
    pcDamage (uniformHost b k q) D < n.choose 2 - balancedPairs ∧
    lccDamage (uniformHost b k q) D < n - q
  obtain ⟨⟨C, hLarge⟩, hSquares⟩ :=
    uniform_fewer_tail_components_strict_optimizer_bounds hb hk hq D hD hJ
  have hTotal : (∑ C : G.ConnectedComponent, c C) = S := by
    calc
      _ = Fintype.card (survivors D) := sum_component_card G
      _ = (Dᶜ).card := Fintype.card_ofFinset _ (by simp [survivors])
      _ = S := uniform_survivor_card hq D hD
  have hPairs : 2 * pairs + S = ∑ C : G.ConnectedComponent, c C ^ 2 := by
    change 2 * (∑ C : G.ConnectedComponent, (c C).choose 2) + S = _
    rw [← hTotal, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun C _ => twice_choose_two_add (c C)
  have hBalanced : 2 * balancedPairs + S = (b + 1) * q ^ 2 := by
    calc
      _ = (b + 1) * (2 * q.choose 2 + q) := by dsimp [balancedPairs, S]; ring
      _ = _ := by rw [twice_choose_two_add]
  have hStrictPairs : balancedPairs < pairs := by
    change (b + 1) * q ^ 2 < ∑ C : G.ConnectedComponent, c C ^ 2 at hSquares
    omega
  have hSn : S ≤ n := by
    simpa only [uniform_survivor_card hq D hD] using Finset.card_le_univ (Dᶜ)
  have hPrefixPos : 0 < (2 * b) * (k + 2) := Nat.mul_pos (by omega) (by omega)
  have hqPos : 0 < q := by omega
  have hqS : q < S := by
    change q < (b + 1) * q
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.lt_add_of_pos_left (Nat.mul_pos (by omega) hqPos)
  have hSqS : (b + 1) * q ^ 2 < S ^ 2 := by
    have hFactor : b + 1 < (b + 1) * (b + 1) := by
      rw [Nat.add_mul b 1 (b + 1), Nat.one_mul]
      exact Nat.lt_add_of_pos_left (Nat.mul_pos (by omega) (by omega))
    calc
      _ < ((b + 1) * (b + 1)) * q ^ 2 :=
        Nat.mul_lt_mul_of_pos_right hFactor (Nat.pow_pos hqPos)
      _ = S ^ 2 := by dsimp [S]; ring
  have hBalancedPositive : balancedPairs < n.choose 2 := by
    have hChooseS := twice_choose_two_add S
    have hChooseLe := Nat.choose_le_choose 2 hSn
    omega
  refine ⟨hStrictPairs, ?_, ?_⟩
  · have hActual : ((componentSizes (uniformHost b k q) D).map (fun s => s.choose 2)).sum =
        pairs := by
      simp only [componentSizes, Multiset.map_map, Function.comp_def, pairs, c, G,
        Finset.sum_eq_multiset_sum]
    change n.choose 2 -
        ((componentSizes (uniformHost b k q) D).map (fun s => s.choose 2)).sum <
      n.choose 2 - balancedPairs
    rw [hActual]
    omega
  · have hSizeMem : c C ∈ componentSizes (uniformHost b k q) D :=
      Multiset.mem_map.mpr ⟨C, Finset.mem_univ _, rfl⟩
    have hSup : q < (componentSizes (uniformHost b k q) D).sup :=
      hLarge.trans_le (Multiset.le_sup hSizeMem)
    change n - (componentSizes (uniformHost b k q) D).sup < n - q
    omega

end Ugurlu33528
