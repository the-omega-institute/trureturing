/- GID: D5/S3/Geometry/FiniteGraphSuspensionMoves/Lozin
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGraphSuspensionMoves/Lozin
   mirror-E: none(waiver:finite-graph-singular-homology)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Subgraph]
   utility: none
   digest: A literal Lozin replacement and its exact star-subgraph suspension identification. -/
import D5.S3.Geometry.FiniteGraphSuspensionMoves.EdgeMatching

/-!
# Lozin replacements

The classical Lozin suspension is attributed to Biyikoglu--Civan,
Proposition 3.4. Its graph is identified explicitly with the arbitrary local
star-subgraph gadget of Barmak, Proposition 7.2. Ambient edges inside the
selected leaf set are retained.
-/

noncomputable section
open CategoryTheory

namespace D5.S3.Geometry.FiniteGraphSuspensionMoves

open FiniteGraphSubgraphSuspension

variable {V : Type} [Fintype V] [DecidableEq V]

private theorem star_center_not_leaf (G : SimpleGraph V) (v : V) (Y : Finset V)
    (hY : ∀ x ∈ Y, G.Adj v x) : v ∉ Y :=
  fun hv => G.irrefl (hY v hv)

def starEmbedding (v : V) (Y : Finset V) (hvY : v ∉ Y) : Option ↥Y ↪ V where
  toFun x := match x with | none => v | some x => x.val
  inj' := by
    intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b =>
        change v = b.val at h
        exact False.elim (hvY (h.symm ▸ b.property))
    | some a =>
      cases b with
      | none =>
        change a.val = v at h
        exact False.elim (hvY (h ▸ a.property))
      | some b => exact congrArg some (Subtype.ext h)

private theorem star_embedding_adj (G : SimpleGraph V) (v : V) (Y : Finset V)
    (hY : ∀ x ∈ Y, G.Adj v x) :
    ∀ a b, (starModel ↥Y).Adj a b →
      G.Adj (starEmbedding v Y (star_center_not_leaf G v Y hY) a)
        (starEmbedding v Y (star_center_not_leaf G v Y hY) b) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => exact False.elim h
    | some b => exact hY b.val b.property
  | some a =>
    cases b with
    | none => exact G.adj_symm (hY a.val a.property)
    | some b => exact False.elim h

def starSubgraph (G : SimpleGraph V) (v : V) (Y : Finset V)
    (hY : ∀ x ∈ Y, G.Adj v x) : G.Subgraph :=
  embeddedSubgraph G (starModel ↥Y)
    (starEmbedding v Y (star_center_not_leaf G v Y hY)) (star_embedding_adj G v Y hY)

def starApexEquiv (G : SimpleGraph V) (v : V) (Y : Finset V)
    (hY : ∀ x ∈ Y, G.Adj v x) (hYn : Y.Nonempty) :
    Bool ≃ MaxIndependent (starSubgraph G v Y hY).coe := by
  letI : Nonempty ↥Y := ⟨⟨hYn.choose, hYn.choose_spec⟩⟩
  exact (starMaxEquiv ↥Y).trans (maxEquiv
    (embeddedIso G (starModel ↥Y)
      (starEmbedding v Y (star_center_not_leaf G v Y hY)) (star_embedding_adj G v Y hY)))

theorem star_removed (G : SimpleGraph V) (v : V) (Y : Finset V)
    (hY : ∀ x ∈ Y, G.Adj v x) (x y : V) :
    (starSubgraph G v Y hY).Adj x y ↔ (x = v ∧ y ∈ Y) ∨ (y = v ∧ x ∈ Y) := by
  change (∃ s t, (starModel ↥Y).Adj s t ∧
    starEmbedding v Y _ s = x ∧ starEmbedding v Y _ t = y) ↔ _
  constructor
  · rintro ⟨s, t, h, hs, ht⟩
    cases s with
    | none =>
      cases t with
      | none => exact False.elim h
      | some t => exact Or.inl ⟨hs.symm, ht ▸ t.property⟩
    | some s =>
      cases t with
      | none => exact Or.inr ⟨ht.symm, hs ▸ s.property⟩
      | some t => exact False.elim h
  · rintro (⟨rfl, hy⟩ | ⟨rfl, hx⟩)
    · exact ⟨none, some ⟨y, hy⟩, trivial, rfl, rfl⟩
    · exact ⟨some ⟨x, hx⟩, none, trivial, rfl, rfl⟩

theorem star_complement (G : SimpleGraph V) (v : V) (Y : Finset V)
    (hY : ∀ x ∈ Y, G.Adj v x) (hYn : Y.Nonempty) (t : Bool) (x : V) :
    (x ∈ (starSubgraph G v Y hY).verts ∧
      x ∉ (starApexEquiv G v Y hY hYn t).val.image Subtype.val) ↔
      if t then x = v else x ∈ Y := by
  letI : Nonempty ↥Y := ⟨⟨hYn.choose, hYn.choose_spec⟩⟩
  change (x ∈ (embeddedSubgraph G (starModel ↥Y) _ _).verts ∧
    x ∉ (mapMax (embeddedIso G (starModel ↥Y) _ _) (starMax ↥Y t)).val.image Subtype.val) ↔ _
  rw [embedded_complement]
  cases t with
  | false =>
    constructor
    · rintro ⟨s, hs, hm⟩
      cases s with
      | none => simp [starMax] at hm
      | some s => exact hs ▸ s.property
    · intro hx
      exact ⟨some ⟨x, hx⟩, rfl, by simp [starMax]⟩
  | true =>
    constructor
    · rintro ⟨s, hs, hm⟩
      cases s with
      | none => exact hs.symm
      | some s => simp [starMax] at hm
    · intro hx
      exact ⟨none, hx.symm, by simp [starMax]⟩

/-- Delete the old vertex v, then add four genuinely fresh path vertices. -/
abbrev LozinVertex (v : V) := {x : V // x ≠ v} ⊕ Fin 4

private def lozinAdj (G : SimpleGraph V) (v : V) (Y Z : Finset V) :
    LozinVertex v → LozinVertex v → Prop
  | .inl x, .inl y => G.Adj x.val y.val
  | .inl x, .inr i => (i = 0 ∧ x.val ∈ Y) ∨ (i = 3 ∧ x.val ∈ Z)
  | .inr i, .inl x => (i = 0 ∧ x.val ∈ Y) ∨ (i = 3 ∧ x.val ∈ Z)
  | .inr i, .inr j => i.val + 1 = j.val ∨ j.val + 1 = i.val

/-- The literal path y(0)--a(1)--b(2)--z(3), with attachments to Y and Z. -/
def lozinSuspension (G : SimpleGraph V) (v : V) (Y Z : Finset V) :
    SimpleGraph (LozinVertex v) where
  Adj := lozinAdj G v Y Z
  symm.symm := by
    rintro (x | i) (y | j)
    · exact G.adj_symm
    · exact id
    · exact id
    · exact Or.symm
  loopless.irrefl := by
    rintro (x | i)
    · exact G.irrefl
    · simp [lozinAdj]

/-- The actual cardinality-preserving bijection. Old vertices other than v
stay fixed. The deleted old v is identified with the final path vertex z. -/
def lozinBaseEquiv (v : V) : LozinVertex v ≃ (V ⊕ Fin 3) where
  toFun x := match x with
    | .inl x => .inl x.val
    | .inr i => ![Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inl v] i
  invFun x := match x with
    | .inl x => if hx : x = v then .inr 3 else .inl ⟨x, hx⟩
    | .inr i => .inr i.castSucc
  left_inv := by
    rintro (x | i)
    · simp [x.property]
    · fin_cases i <;> simp
  right_inv := by
    rintro (x | i)
    · by_cases hx : x = v <;> simp [hx]
    · fin_cases i <;> simp

/-- Extract the star edges from the exact input neighbor partition. -/
def partitionYAdj (G : SimpleGraph V) (v : V) (Y Z : Finset V)
    (hpart : ∀ x, G.Adj v x ↔ x ∈ Y ∨ x ∈ Z) : ∀ x ∈ Y, G.Adj v x :=
  fun x hx => (hpart x).mpr (Or.inl hx)

def lozinVertexEquiv (G : SimpleGraph V) (v : V) (Y Z : Finset V)
    (hpart : ∀ x, G.Adj v x ↔ x ∈ Y ∨ x ∈ Z) (hYn : Y.Nonempty) :
    LozinVertex v ≃
      (V ⊕ Option (MaxIndependent (starSubgraph G v Y (partitionYAdj G v Y Z hpart)).coe)) :=
  (lozinBaseEquiv v).trans (Equiv.sumCongr (Equiv.refl V)
    (tripleNewCode.trans (Equiv.optionCongr
      (starApexEquiv G v Y (partitionYAdj G v Y Z hpart) hYn))))

private theorem retained_old (G : SimpleGraph V) (v : V) (Y : Finset V)
    (hY : ∀ x ∈ Y, G.Adj v x) (x y : V) (hx : x ≠ v) (hy : y ≠ v) :
    (G.Adj x y ∧ ¬ (starSubgraph G v Y hY).Adj x y) ↔ G.Adj x y := by
  simp [star_removed, hx, hy]

private theorem retained_center (G : SimpleGraph V) (v : V) (Y Z : Finset V)
    (hpart : ∀ x, G.Adj v x ↔ x ∈ Y ∨ x ∈ Z) (hdisj : Disjoint Y Z)
    (x : V) (hx : x ≠ v) :
    (G.Adj x v ∧ ¬ (starSubgraph G v Y (partitionYAdj G v Y Z hpart)).Adj x v) ↔
      x ∈ Z := by
  rw [star_removed]
  simp only [hx, false_and, true_and, false_or]
  rw [G.adj_comm x v, hpart x]
  constructor
  · rintro ⟨h, hn⟩; exact h.resolve_left hn
  · intro hz
    exact ⟨Or.inr hz, fun hy => Finset.disjoint_left.mp hdisj hy hz⟩

/-- Exact Lozin/star-gadget identification. Y need only be nonempty; Z may
be empty. In particular there is no hypothesis about G induced on Y. -/
def lozinSuspensionIso (G : SimpleGraph V) (v : V) (Y Z : Finset V)
    (hpart : ∀ x, G.Adj v x ↔ x ∈ Y ∨ x ∈ Z) (hdisj : Disjoint Y Z)
    (hYn : Y.Nonempty) :
    lozinSuspension G v Y Z ≃g
      localSuspensionGraph G (starSubgraph G v Y (partitionYAdj G v Y Z hpart)) where
  toEquiv := lozinVertexEquiv G v Y Z hpart hYn
  map_rel_iff' := by
    let H := starSubgraph G v Y (partitionYAdj G v Y Z hpart)
    let E := lozinVertexEquiv G v Y Z hpart hYn
    have hvY : v ∉ Y := star_center_not_leaf G v Y (partitionYAdj G v Y Z hpart)
    have mixed (x : {x : V // x ≠ v}) (j : Fin 4) :
        (localSuspensionGraph G H).Adj (E (.inl x)) (E (.inr j)) ↔
          (lozinSuspension G v Y Z).Adj (.inl x) (.inr j) := by
      fin_cases j
      · change (x.val ∈ H.verts ∧
          x.val ∉ (starApexEquiv G v Y (partitionYAdj G v Y Z hpart) hYn false).val.image
            Subtype.val) ↔ _
        rw [star_complement]
        simp [lozinSuspension, lozinAdj]
      · change False ↔ _
        simp [lozinSuspension, lozinAdj]
      · change (x.val ∈ H.verts ∧
          x.val ∉ (starApexEquiv G v Y (partitionYAdj G v Y Z hpart) hYn true).val.image
            Subtype.val) ↔ _
        rw [star_complement]
        simp [lozinSuspension, lozinAdj, x.property]
      · change (G.Adj x.val v ∧ ¬ H.Adj x.val v) ↔ _
        rw [retained_center G v Y Z hpart hdisj x.val x.property]
        simp [lozinSuspension, lozinAdj]
    rintro (x | i) (y | j)
    · change (G.Adj x.val y.val ∧ ¬ H.Adj x.val y.val) ↔ G.Adj x.val y.val
      exact retained_old G v Y (partitionYAdj G v Y Z hpart)
        x.val y.val x.property y.property
    · exact mixed x j
    · exact ((localSuspensionGraph G H).adj_comm _ _).trans
        ((mixed y i).trans ((lozinSuspension G v Y Z).adj_comm _ _))
    · fin_cases i <;> fin_cases j
      all_goals
        first
        | change (v ∈ H.verts ∧
            v ∉ (starApexEquiv G v Y (partitionYAdj G v Y Z hpart) hYn false).val.image
              Subtype.val) ↔ _
          rw [star_complement]
          simp [lozinSuspension, lozinAdj, hvY]
        | change (v ∈ H.verts ∧
            v ∉ (starApexEquiv G v Y (partitionYAdj G v Y Z hpart) hYn true).val.image
              Subtype.val) ↔ _
          rw [star_complement]
          simp [lozinSuspension, lozinAdj]
        | simp [E, H, lozinVertexEquiv, lozinBaseEquiv, tripleNewCode,
            lozinSuspension, lozinAdj, hvY]

def lozinSuspensionReducedHomologyIso (G : SimpleGraph V) (v : V) (Y Z : Finset V)
    (hpart : ∀ x, G.Adj v x ↔ x ∈ Y ∨ x ∈ Z) (hdisj : Disjoint Y Z)
    (hYn : Y.Nonempty) (q : ℕ) (hq : 1 ≤ q) :
    Reduced (lozinSuspension G v Y Z) (q + 1) ≅ Reduced G q := by
  letI : Nonempty V := ⟨v⟩
  letI : Fintype (starSubgraph G v Y (partitionYAdj G v Y Z hpart)).verts :=
    Fintype.ofFinite _
  exact graphReducedIso (lozinSuspensionIso G v Y Z hpart hdisj hYn) (q + 1) ≪≫
    localSubgraphReducedHomologyIso G
      (starSubgraph G v Y (partitionYAdj G v Y Z hpart)) q hq

end D5.S3.Geometry.FiniteGraphSuspensionMoves
