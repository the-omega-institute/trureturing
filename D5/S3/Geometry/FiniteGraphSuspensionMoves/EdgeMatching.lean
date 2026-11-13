/- GID: D5/S3/Geometry/FiniteGraphSuspensionMoves/EdgeMatching
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGraphSuspensionMoves/EdgeMatching
   mirror-E: none(waiver:finite-graph-singular-homology)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Subgraph]
   utility: none
   digest: Literal triple subdivisions and crossing suspensions identified with arbitrary-subgraph gadgets. -/
import D5.S3.Geometry.FiniteGraphSuspensionMoves.Models

/-!
# Triple subdivisions and matching suspensions

Three fresh path vertices, or a hub and four fresh quadrant vertices, give
literal graphs isomorphic to arbitrary local-subgraph suspension gadgets.
All old edges outside the chosen subgraph are retained. The matching need
not be induced. The reduced integral singular homology shift follows from
the local gadget construction of Barmak, Proposition 7.2.
-/

noncomputable section
open CategoryTheory

namespace D5.S3.Geometry.FiniteGraphSuspensionMoves

open FiniteGraphSubgraphSuspension FiniteGraphVertexSubstitution FiniteCoordinateTruncation

variable {V : Type} [Fintype V] [DecidableEq V]

def edgeEmbedding (a b : V) (hne : a ≠ b) : Bool ↪ V where
  toFun t := if t then b else a
  inj' := by
    intro s t h
    cases s <;> cases t <;> simp_all

private theorem edge_embedding_adj (G : SimpleGraph V) {a b : V} (hab : G.Adj a b) :
    ∀ s t, edgeModel.Adj s t →
      G.Adj (edgeEmbedding a b hab.ne s) (edgeEmbedding a b hab.ne t) := by
  intro s t h
  change G.Adj (if s then b else a) (if t then b else a)
  cases s <;> cases t <;> simp_all [edgeModel, G.adj_comm]

def edgeSubgraph (G : SimpleGraph V) {a b : V} (hab : G.Adj a b) : G.Subgraph :=
  embeddedSubgraph G edgeModel (edgeEmbedding a b hab.ne) (edge_embedding_adj G hab)

def edgeApexEquiv (G : SimpleGraph V) {a b : V} (hab : G.Adj a b) :
    Bool ≃ MaxIndependent (edgeSubgraph G hab).coe :=
  edgeMaxEquiv.trans (maxEquiv (embeddedIso G edgeModel
    (edgeEmbedding a b hab.ne) (edge_embedding_adj G hab)))

theorem edge_removed (G : SimpleGraph V) {a b : V} (hab : G.Adj a b) (x y : V) :
    (edgeSubgraph G hab).Adj x y ↔ (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  change (∃ s t, edgeModel.Adj s t ∧
    edgeEmbedding a b hab.ne s = x ∧ edgeEmbedding a b hab.ne t = y) ↔ _
  constructor
  · rintro ⟨s, t, h, hs, ht⟩
    change (if s then b else a) = x at hs
    change (if t then b else a) = y at ht
    cases s <;> cases t <;> simp_all [edgeModel]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨false, true, by simp [edgeModel], rfl, rfl⟩
    · exact ⟨true, false, by simp [edgeModel], rfl, rfl⟩

theorem edge_complement (G : SimpleGraph V) {a b : V} (hab : G.Adj a b)
    (t : Bool) (x : V) :
    (x ∈ (edgeSubgraph G hab).verts ∧
      x ∉ (edgeApexEquiv G hab t).val.image Subtype.val) ↔
      x = edgeEmbedding a b hab.ne t := by
  change (x ∈ (embeddedSubgraph G edgeModel _ _).verts ∧
    x ∉ (mapMax (embeddedIso G edgeModel _ _) (edgeMax t)).val.image Subtype.val) ↔ _
  rw [embedded_complement]
  constructor
  · rintro ⟨s, hs, hm⟩
    have hst : s = t := by cases s <;> cases t <;> simp_all [edgeMax, edgeSet]
    exact hst ▸ hs.symm
  · intro hx
    exact ⟨t, hx.symm, by cases t <;> simp [edgeMax, edgeSet]⟩

private def tripleAdj (G : SimpleGraph V) (a b : V) :
    (V ⊕ Fin 3) → (V ⊕ Fin 3) → Prop
  | .inl x, .inl y => G.Adj x y ∧ ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))
  | .inl x, .inr i => (i = 0 ∧ x = a) ∨ (i = 2 ∧ x = b)
  | .inr i, .inl x => (i = 0 ∧ x = a) ∨ (i = 2 ∧ x = b)
  | .inr i, .inr j => i.val + 1 = j.val ∨ j.val + 1 = i.val

/-- Remove precisely a--b and add a--0--1--2--b. The sum type makes all
three inserted vertices fresh, even for a finite Nat-labeled old graph. -/
def tripleSubdivision (G : SimpleGraph V) (a b : V) : SimpleGraph (V ⊕ Fin 3) where
  Adj := tripleAdj G a b
  symm.symm := by
    rintro (x | i) (y | j)
    · rintro ⟨h, hn⟩
      exact ⟨G.adj_symm h, by simpa [tripleAdj, and_comm, or_comm] using hn⟩
    · exact id
    · exact id
    · exact Or.symm
  loopless.irrefl := by
    rintro (x | i)
    · exact fun h => G.irrefl h.1
    · simp [tripleAdj]

def tripleNewCode : Fin 3 ≃ Option Bool :=
  Equiv.ofBijective (fun i => ![some false, none, some true] i) (by decide)

def tripleVertexEquiv (G : SimpleGraph V) {a b : V} (hab : G.Adj a b) :
    (V ⊕ Fin 3) ≃ (V ⊕ Option (MaxIndependent (edgeSubgraph G hab).coe)) :=
  Equiv.sumCongr (Equiv.refl V)
    (tripleNewCode.trans (Equiv.optionCongr (edgeApexEquiv G hab)))

/-- The hub is path vertex 1; apices adjacent to a and b are path vertices
0 and 2. This proves the missing graph identification, without inducedness. -/
def tripleSubdivisionIso (G : SimpleGraph V) {a b : V} (hab : G.Adj a b) :
    tripleSubdivision G a b ≃g localSuspensionGraph G (edgeSubgraph G hab) where
  toEquiv := tripleVertexEquiv G hab
  map_rel_iff' := by
    rintro (x | i) (y | j)
    · change (localSuspensionGraph G (edgeSubgraph G hab)).Adj (.inl x) (.inl y) ↔ _
      simp [tripleSubdivision, tripleAdj, edge_removed]
    · fin_cases j
      · change (x ∈ (edgeSubgraph G hab).verts ∧
          x ∉ (edgeApexEquiv G hab false).val.image Subtype.val) ↔
          ((0 : Fin 3) = 0 ∧ x = a) ∨ ((0 : Fin 3) = 2 ∧ x = b)
        rw [edge_complement]
        change (x = a) ↔ _
        simp
      · change False ↔ ((1 : Fin 3) = 0 ∧ x = a) ∨ ((1 : Fin 3) = 2 ∧ x = b)
        simp
      · change (x ∈ (edgeSubgraph G hab).verts ∧
          x ∉ (edgeApexEquiv G hab true).val.image Subtype.val) ↔
          ((2 : Fin 3) = 0 ∧ x = a) ∨ ((2 : Fin 3) = 2 ∧ x = b)
        rw [edge_complement]
        change (x = b) ↔ _
        simp
    · fin_cases i
      · change (y ∈ (edgeSubgraph G hab).verts ∧
          y ∉ (edgeApexEquiv G hab false).val.image Subtype.val) ↔
          ((0 : Fin 3) = 0 ∧ y = a) ∨ ((0 : Fin 3) = 2 ∧ y = b)
        rw [edge_complement]
        change (y = a) ↔ _
        simp
      · change False ↔ ((1 : Fin 3) = 0 ∧ y = a) ∨ ((1 : Fin 3) = 2 ∧ y = b)
        simp
      · change (y ∈ (edgeSubgraph G hab).verts ∧
          y ∉ (edgeApexEquiv G hab true).val.image Subtype.val) ↔
          ((2 : Fin 3) = 0 ∧ y = a) ∨ ((2 : Fin 3) = 2 ∧ y = b)
        rw [edge_complement]
        change (y = b) ↔ _
        simp
    · fin_cases i <;> fin_cases j <;>
        simp [tripleVertexEquiv, tripleNewCode, tripleSubdivision, tripleAdj]

section Crossing

variable (G : SimpleGraph V) (e : (Bool × Bool) ↪ V)
  (hab : G.Adj (e (false, false)) (e (false, true)))
  (hcd : G.Adj (e (true, false)) (e (true, true)))

include hab hcd in
private theorem matching_embedding_adj : ∀ x y, matchingModel.Adj x y → G.Adj (e x) (e y) := by
  rintro ⟨i, s⟩ ⟨j, t⟩ ⟨hij, hst⟩
  dsimp at hij hst
  subst j
  cases i <;> cases s <;> cases t <;> simp_all [G.adj_comm]

def matchingSubgraph : G.Subgraph :=
  embeddedSubgraph G matchingModel e (matching_embedding_adj G e hab hcd)

def crossingApexEquiv : (Bool × Bool) ≃ MaxIndependent (matchingSubgraph G e hab hcd).coe :=
  quadrantMaxEquiv.trans (maxEquiv
    (embeddedIso G matchingModel e (matching_embedding_adj G e hab hcd)))

def matchingRemoved (x y : V) : Prop :=
  (x = e (false, false) ∧ y = e (false, true)) ∨
  (x = e (false, true) ∧ y = e (false, false)) ∨
  (x = e (true, false) ∧ y = e (true, true)) ∨
  (x = e (true, true) ∧ y = e (true, false))

theorem matching_removed (x y : V) :
    (matchingSubgraph G e hab hcd).Adj x y ↔ matchingRemoved e x y := by
  change (∃ p q, matchingModel.Adj p q ∧ e p = x ∧ e q = y) ↔ _
  constructor
  · rintro ⟨⟨i, s⟩, ⟨j, t⟩, h, hp, hq⟩
    change i = j ∧ s ≠ t at h
    rcases h with ⟨rfl, hst⟩
    cases i <;> cases s <;> cases t <;> simp_all [matchingRemoved]
  · intro h
    rcases h with h | h | h | h
    · exact ⟨(false, false), (false, true), by decide, h.1.symm, h.2.symm⟩
    · exact ⟨(false, true), (false, false), by decide, h.1.symm, h.2.symm⟩
    · exact ⟨(true, false), (true, true), by decide, h.1.symm, h.2.symm⟩
    · exact ⟨(true, true), (true, false), by decide, h.1.symm, h.2.symm⟩

theorem crossing_complement (p : Bool × Bool) (x : V) :
    (x ∈ (matchingSubgraph G e hab hcd).verts ∧
      x ∉ (crossingApexEquiv G e hab hcd p).val.image Subtype.val) ↔
      x = e (false, p.1) ∨ x = e (true, p.2) := by
  change (x ∈ (embeddedSubgraph G matchingModel _ _).verts ∧
    x ∉ (mapMax (embeddedIso G matchingModel _ _) (quadrantMax p)).val.image Subtype.val) ↔ _
  rw [embedded_complement]
  constructor
  · rintro ⟨⟨i, b⟩, hx, hm⟩
    rcases p with ⟨s, t⟩
    cases i <;> cases b <;> cases s <;> cases t <;>
      simp_all [quadrantMax, quadrantSet]
  · rintro (hx | hx)
    · refine ⟨(false, p.1), hx.symm, ?_⟩
      rcases p with ⟨s, t⟩
      cases s <;> cases t <;> simp [quadrantMax, quadrantSet]
    · refine ⟨(true, p.2), hx.symm, ?_⟩
      rcases p with ⟨s, t⟩
      cases s <;> cases t <;> simp [quadrantMax, quadrantSet]

end Crossing

private def crossingAdj (G : SimpleGraph V) (e : (Bool × Bool) ↪ V) :
    (V ⊕ Option (Bool × Bool)) → (V ⊕ Option (Bool × Bool)) → Prop
  | .inl x, .inl y => G.Adj x y ∧ ¬ matchingRemoved e x y
  | .inl _, .inr none => False
  | .inr none, .inl _ => False
  | .inl x, .inr (some p) => x = e (false, p.1) ∨ x = e (true, p.2)
  | .inr (some p), .inl x => x = e (false, p.1) ∨ x = e (true, p.2)
  | .inr none, .inr none => False
  | .inr none, .inr (some _) => True
  | .inr (some _), .inr none => True
  | .inr (some _), .inr (some _) => False

/-- The five new vertices are the hub and quadrants (a,c),(a,d),(b,c),(b,d).
Only the two matching edges are removed. Ambient cross edges are retained. -/
def crossingSuspension (G : SimpleGraph V) (e : (Bool × Bool) ↪ V) :
    SimpleGraph (V ⊕ Option (Bool × Bool)) where
  Adj := crossingAdj G e
  symm.symm := by
    rintro (x | p) (y | q)
    · rintro ⟨h, hn⟩
      refine ⟨G.adj_symm h, ?_⟩
      simpa [matchingRemoved, and_comm, or_comm, or_left_comm, or_assoc] using hn
    · cases q <;> exact id
    · cases p <;> exact id
    · cases p <;> cases q <;> exact id
  loopless.irrefl := by
    rintro (x | p)
    · exact fun h => G.irrefl h.1
    · cases p <;> simp [crossingAdj]

def crossingSuspensionIso (G : SimpleGraph V) (e : (Bool × Bool) ↪ V)
    (hab : G.Adj (e (false, false)) (e (false, true)))
    (hcd : G.Adj (e (true, false)) (e (true, true))) :
    crossingSuspension G e ≃g localSuspensionGraph G (matchingSubgraph G e hab hcd) where
  toEquiv := Equiv.sumCongr (Equiv.refl V)
    (Equiv.optionCongr (crossingApexEquiv G e hab hcd))
  map_rel_iff' := by
    rintro (x | p) (y | q)
    · change (localSuspensionGraph G (matchingSubgraph G e hab hcd)).Adj (.inl x) (.inl y) ↔ _
      simp [crossingSuspension, crossingAdj, matching_removed]
    · cases q with
      | none => rfl
      | some p =>
        change (x ∈ (matchingSubgraph G e hab hcd).verts ∧
          x ∉ (crossingApexEquiv G e hab hcd p).val.image Subtype.val) ↔ _
        exact crossing_complement G e hab hcd p x
    · cases p with
      | none => rfl
      | some p =>
        change (y ∈ (matchingSubgraph G e hab hcd).verts ∧
          y ∉ (crossingApexEquiv G e hab hcd p).val.image Subtype.val) ↔ _
        exact crossing_complement G e hab hcd p y
    · cases p <;> cases q <;> rfl

/- The actual graph identifications, not an assumed move-correctness premise,
are consumed by the singular homology shift. -/

abbrev Reduced (G : SimpleGraph V) (q : ℕ) :=
  (TauCeti.reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) q).obj
    (TopCat.of (Ispace G))

/-- The existing realization homeomorphism gives integral singular-homology
transport. Used below and by the concrete replay relabeling interface. -/
def graphReducedIso {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {F : SimpleGraph W} (e : G ≃g F) (q : ℕ) :
    Reduced G q ≅ Reduced F q :=
  (graphIsoHomeomorph e).toHomotopyEquiv.reducedSingularHomologyIso (ModuleCat.of ℤ ℤ) q

def tripleSubdivisionReducedHomologyIso (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) (q : ℕ) (hq : 1 ≤ q) :
    Reduced (tripleSubdivision G a b) (q + 1) ≅ Reduced G q := by
  letI : Nonempty V := ⟨a⟩
  letI : Fintype (edgeSubgraph G hab).verts := Fintype.ofFinite _
  exact graphReducedIso (tripleSubdivisionIso G hab) (q + 1) ≪≫
    localSubgraphReducedHomologyIso G (edgeSubgraph G hab) q hq

def crossingSuspensionReducedHomologyIso (G : SimpleGraph V) (e : (Bool × Bool) ↪ V)
    (hab : G.Adj (e (false, false)) (e (false, true)))
    (hcd : G.Adj (e (true, false)) (e (true, true))) (q : ℕ) (hq : 1 ≤ q) :
    Reduced (crossingSuspension G e) (q + 1) ≅ Reduced G q := by
  letI : Nonempty V := ⟨e (false, false)⟩
  letI : Fintype (matchingSubgraph G e hab hcd).verts := Fintype.ofFinite _
  exact graphReducedIso (crossingSuspensionIso G e hab hcd) (q + 1) ≪≫
    localSubgraphReducedHomologyIso G (matchingSubgraph G e hab hcd) q hq

end D5.S3.Geometry.FiniteGraphSuspensionMoves
