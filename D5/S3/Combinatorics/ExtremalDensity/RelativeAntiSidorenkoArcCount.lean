/- GID: D5/S3/Combinatorics/ExtremalDensity/RelativeAntiSidorenkoArcCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ExtremalDensity/RelativeAntiSidorenkoArcCount
   mirror-E: none(waiver:formal-unit-only)
   anchors: [mathlib/module/Mathlib.Combinatorics.Digraph.Orientation, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected]
   utility: none
   digest: A connected relatively anti-Sidorenko orientation with three modulo four arcs. -/

import Mathlib.Combinatorics.Digraph.Orientation
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic
import D5.S3.Combinatorics.ExtremalDensity.ThreeClassHomomorphismLimit

/-! An affirmative answer to Question 5.3 of Bitonti, Hogan, Noel and Tsarev. -/

set_option autoImplicit false

open scoped BigOperators
open D5.S3.Combinatorics.ExtremalDensity.ThreeClassHomomorphismLimit (homCount)

namespace D5.S3.Combinatorics.ExtremalDensity.RelativeAntiSidorenkoArcCount

noncomputable section

/-- Asymmetry enforces both looplessness and the exclusion of opposite arcs. -/
def Oriented {V : Type*} (G : Digraph V) : Prop :=
  ∀ a b, G.Adj a b → ¬G.Adj b a

private theorem underlying_adj {V : Type*} {G : Digraph V} (hG : Oriented G) {a b : V} :
    G.toSimpleGraphInclusive.Adj a b ↔ G.Adj a b ∨ G.Adj b a := by
  change a ≠ b ∧ (G.Adj a b ∨ G.Adj b a) ↔ _
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rintro rfl
  have ha : G.Adj a a := h.elim id id
  exact hG a a ha ha

/-- The numbering agrees with the explicit witness. Vertex 0 is the shared root. -/
private def arcs : Finset (Fin 13 × Fin 13) :=
  {(0, 3), (1, 3), (0, 4), (4, 1), (5, 0), (1, 5), (6, 0), (6, 1),
   (0, 7), (2, 7), (0, 8), (8, 2), (9, 0), (2, 9), (10, 0), (10, 2),
   (1, 2), (11, 0), (0, 12)}

private def witness : Digraph (Fin 13) where
  Adj u v := (u, v) ∈ arcs

private instance witnessAdjDecidable : DecidableRel witness.Adj :=
  inferInstanceAs (DecidableRel fun u v => (u, v) ∈ arcs)

private instance witnessUnderlyingAdjDecidable : DecidableRel witness.toSimpleGraphInclusive.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel witness.Adj).Adj)

private theorem witness_oriented : Oriented witness := by
  unfold Oriented
  decide

private theorem witness_connected : witness.toSimpleGraphInclusive.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable witness.toSimpleGraphInclusive).mpr
  refine ⟨0, fun i => ?_⟩
  fin_cases i
  · exact SimpleGraph.Reachable.refl _
  · exact (SimpleGraph.Adj.reachable (show witness.toSimpleGraphInclusive.Adj 0 3 by decide)).trans
      (SimpleGraph.Adj.reachable (show witness.toSimpleGraphInclusive.Adj 3 1 by decide))
  · exact (SimpleGraph.Adj.reachable (show witness.toSimpleGraphInclusive.Adj 0 7 by decide)).trans
      (SimpleGraph.Adj.reachable (show witness.toSimpleGraphInclusive.Adj 7 2 by decide))
  all_goals exact SimpleGraph.Adj.reachable (by decide)

/-- Ordered adjacent pairs are the arcs. -/
def arcCount {V : Type*} (G : Digraph V) : ℕ :=
  Nat.card {p : V × V // G.Adj p.1 p.2}

private theorem witness_arcCount : arcCount witness = 19 := by
  unfold arcCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h : Finset.univ.filter (fun p : Fin 13 × Fin 13 => witness.Adj p.1 p.2) = arcs := by
    ext p
    simp [witness]
  rw [h]
  decide

/-- The counted maps have only the adjacency-preservation condition. -/
private def directedHomCount {V W : Type*} (D : Digraph V) (G : Digraph W) : ℕ :=
  Nat.card {f : V → W // ∀ u v, D.Adj u v → G.Adj (f u) (f v)}

private def MapPreserving {V : Type*} (R : V → V → Prop) :=
  {f : Fin 13 → V // ∀ u v, witness.Adj u v → R (f u) (f v)}

private abbrev Extensions {V : Type*} (R : V → V → Prop) (x y : V) :=
  {w // R x w ∧ R y w} × {w // R x w ∧ R w y} ×
  {w // R w x ∧ R y w} × {w // R w x ∧ R w y}

private abbrev Leaves {V : Type*} (R : V → V → Prop) (x : V) :=
  {w // R w x} × {w // R x w}

private abbrev RootedMaps {V : Type*} (R : V → V → Prop) :=
  Σ x y z : V, Subtype (fun _ : Unit => R y z) × Extensions R x y × Extensions R x z × Leaves R x

/-- Every argument in an arc condition is one of the entries of the assembled vertex map. -/
private def assemble {V : Type*} {R : V → V → Prop} (x y z : V) (a : Extensions R x y)
    (b : Extensions R x z) (s : Leaves R x) : Fin 13 → V :=
  ![x, y, z, a.1.val, a.2.1.val, a.2.2.1.val, a.2.2.2.val,
    b.1.val, b.2.1.val, b.2.2.1.val, b.2.2.2.val, s.1.val, s.2.val]

private theorem assemble_preserves {V : Type*} {R : V → V → Prop} {x y z : V}
    (edge : R y z) (a : Extensions R x y) (b : Extensions R x z) (s : Leaves R x) :
    ∀ u v, witness.Adj u v → R (assemble x y z a b s u) (assemble x y z a b s v) := by
  intro u v h
  simp only [witness, arcs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact a.1.property.1
  · exact a.1.property.2
  · exact a.2.1.property.1
  · exact a.2.1.property.2
  · exact a.2.2.1.property.1
  · exact a.2.2.1.property.2
  · exact a.2.2.2.property.1
  · exact a.2.2.2.property.2
  · exact b.1.property.1
  · exact b.1.property.2
  · exact b.2.1.property.1
  · exact b.2.1.property.2
  · exact b.2.2.1.property.1
  · exact b.2.2.1.property.2
  · exact b.2.2.2.property.1
  · exact b.2.2.2.property.2
  · exact edge
  · exact s.1.property
  · exact s.2.property

private def splitMap {V : Type*} {R : V → V → Prop} (f : MapPreserving R) : RootedMaps R :=
  ⟨f.val 0, f.val 1, f.val 2, ⟨(), f.property 1 2 (by decide)⟩,
    ⟨⟨f.val 3, f.property 0 3 (by decide), f.property 1 3 (by decide)⟩,
     ⟨f.val 4, f.property 0 4 (by decide), f.property 4 1 (by decide)⟩,
     ⟨f.val 5, f.property 5 0 (by decide), f.property 1 5 (by decide)⟩,
     ⟨f.val 6, f.property 6 0 (by decide), f.property 6 1 (by decide)⟩⟩,
    ⟨⟨f.val 7, f.property 0 7 (by decide), f.property 2 7 (by decide)⟩,
     ⟨f.val 8, f.property 0 8 (by decide), f.property 8 2 (by decide)⟩,
     ⟨f.val 9, f.property 9 0 (by decide), f.property 2 9 (by decide)⟩,
     ⟨f.val 10, f.property 10 0 (by decide), f.property 10 2 (by decide)⟩⟩,
    ⟨f.val 11, f.property 11 0 (by decide)⟩, ⟨f.val 12, f.property 0 12 (by decide)⟩⟩

private def mapEquiv {V : Type*} (R : V → V → Prop) : MapPreserving R ≃ RootedMaps R where
  toFun := splitMap
  invFun := fun ⟨x, y, z, edge, a, b, s⟩ => ⟨assemble x y z a b s,
    assemble_preserves edge.property a b s⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv := by
    rintro ⟨x, y, z, ⟨⟨⟩, edge⟩, ⟨a₁, a₂, a₃, a₄⟩, ⟨b₁, b₂, b₃, b₄⟩, s⟩
    rfl

/-- Forgetting the orientation of the source yields exactly the arc conditions
    with a symmetric target relation. -/
private theorem map_underlying_iff {V : Type*} (H : SimpleGraph V) (f : Fin 13 → V) :
    (∀ u v, witness.toSimpleGraphInclusive.Adj u v → H.Adj (f u) (f v)) ↔
    (∀ u v, witness.Adj u v → H.Adj (f u) (f v)) := by
  constructor
  · intro h u v huv
    exact h u v (underlying_adj witness_oriented |>.mpr (Or.inl huv))
  · intro h u v huv
    rcases underlying_adj witness_oriented |>.mp huv with huv | hvu
    · exact h u v huv
    · exact (h v u hvu).symm

/-- Reindex the host by a finite type equivalence to use the project's hom count. -/
private theorem homCount_relabel_host {V : Type*} {n m : ℕ} (D : SimpleGraph (Fin m))
    (G : SimpleGraph V) (e : V ≃ Fin n) :
    homCount D (G.comap e.symm) =
      Nat.card {f : Fin m → V // ∀ u v, D.Adj u v → G.Adj (f u) (f v)} := by
  unfold homCount
  apply Nat.card_congr
  exact
    { toFun := fun f => ⟨fun v => e.symm (f.val v), f.property⟩
      invFun := fun f => ⟨fun v => e (f.val v), by
        intro u v h
        change G.Adj (e.symm (e (f.val u))) (e.symm (e (f.val v)))
        simpa only [e.symm_apply_apply] using f.property u v h⟩
      left_inv := by intro f; apply Subtype.ext; funext i; simp
      right_inv := by intro f; apply Subtype.ext; funext i; simp }

open Classical

private def indicator (p : Prop) : ℕ :=
  if p then 1 else 0

private def size {V : Type*} (p : V → Prop) : ℕ :=
  Nat.card {v // p v}

private theorem size_eq_sum {V : Type*} [Fintype V] (p : V → Prop) :
    size p = ∑ w, indicator (p w) := by
  rw [size, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

private theorem size_congr {V : Type*} {p q : V → Prop} (h : ∀ w, p w ↔ q w) :
    size p = size q :=
  Nat.card_congr (Equiv.subtypeEquivRight h)

private theorem card_arc_condition (p : Prop) :
    Fintype.card (Subtype (fun _ : Unit => p)) = indicator p := by
  rw [← Nat.card_eq_fintype_card]
  change size (fun _ : Unit => p) = _
  simp [size_eq_sum]

private def extensionsCount {V : Type*} (R : V → V → Prop) (x y : V) : ℕ :=
  size (fun w => R x w ∧ R y w) * size (fun w => R x w ∧ R w y) *
  size (fun w => R w x ∧ R y w) * size (fun w => R w x ∧ R w y)

private def leafCount {V : Type*} (R : V → V → Prop) (x : V) : ℕ :=
  size (R · x) * size (R x)

private def middleCount {V : Type*} [Fintype V] (R : V → V → Prop) (x : V) : ℕ :=
  ∑ y, ∑ z, indicator (R y z) * extensionsCount R x y * extensionsCount R x z

/-- Exact count by the images of vertices 0, 1 and 2. The product counts independent
    choices of the eight private vertices and the two leaves. -/
private theorem mapCount_eq_sum {V : Type*} [Fintype V] (R : V → V → Prop) :
    Nat.card (MapPreserving R) = ∑ x, middleCount R x * leafCount R x := by
  classical
  rw [Nat.card_congr (mapEquiv R)]
  unfold RootedMaps
  simp only [Nat.card_sigma, Nat.card_prod, middleCount, leafCount,
    Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ =>
    Finset.sum_congr rfl (fun z _ => ?_)))
  simp only [card_arc_condition, extensionsCount, size, Nat.card_eq_fintype_card]
  ac_rfl

private theorem directed_count_eq_sum {V : Type*} [Fintype V] (G : Digraph V) :
    directedHomCount witness G = ∑ x, middleCount G.Adj x * leafCount G.Adj x :=
  mapCount_eq_sum G.Adj

private theorem undirected_count_eq_sum {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Nat.card {f : Fin 13 → V // ∀ u v, witness.toSimpleGraphInclusive.Adj u v →
      G.Adj (f u) (f v)} = ∑ x, middleCount G.Adj x * leafCount G.Adj x := by
  rw [← mapCount_eq_sum G.Adj]
  exact Nat.card_congr (Equiv.subtypeEquivRight (map_underlying_iff G))

private theorem indicator_underlying {V : Type*} {G : Digraph V} (hG : Oriented G) (a b : V) :
    indicator (G.toSimpleGraphInclusive.Adj a b) =
      indicator (G.Adj a b) + indicator (G.Adj b a) := by
  rw [show G.toSimpleGraphInclusive.Adj a b = (G.Adj a b ∨ G.Adj b a) from
    propext (underlying_adj hG)]
  by_cases hab : G.Adj a b
  · simp [indicator, hab, hG a b hab]
  · by_cases hba : G.Adj b a <;> simp [indicator, hab, hba]

private theorem indicator_and (p q : Prop) :
    indicator (p ∧ q) = indicator p * indicator q := by
  by_cases hp : p <;> by_cases hq : q <;> simp [indicator, hp, hq]

private theorem common_neighbors_partition {V : Type*} [Fintype V] {G : Digraph V}
    (hG : Oriented G) (x y : V) :
    size (fun w => G.toSimpleGraphInclusive.Adj x w ∧ G.toSimpleGraphInclusive.Adj y w) =
      size (fun w => G.Adj x w ∧ G.Adj y w) + size (fun w => G.Adj x w ∧ G.Adj w y) +
      (size (fun w => G.Adj w x ∧ G.Adj y w) + size (fun w => G.Adj w x ∧ G.Adj w y)) := by
  simp only [size_eq_sum, indicator_and, indicator_underlying hG, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w _ => by ring)

private theorem two_amgm (a b : ℕ) : 4 * (a * b) ≤ (a + b) ^ 2 := by
  zify
  nlinarith [sq_nonneg ((a : ℤ) - b)]

private theorem four_amgm (a b c d : ℕ) :
    2 ^ 8 * (a * b * c * d) ≤ (a + b + (c + d)) ^ 4 := by
  have pairBound : 16 * (a * b * c * d) ≤ (a + b) ^ 2 * (c + d) ^ 2 := by
    calc
      _ = (4 * (a * b)) * (4 * (c * d)) := by ring
      _ ≤ _ := Nat.mul_le_mul (two_amgm a b) (two_amgm c d)
  calc
    _ = 16 * (16 * (a * b * c * d)) := by ring
    _ ≤ 16 * ((a + b) ^ 2 * (c + d) ^ 2) := Nat.mul_le_mul_left _ pairBound
    _ = (4 * ((a + b) * (c + d))) ^ 2 := by ring
    _ ≤ ((a + b + (c + d)) ^ 2) ^ 2 := Nat.pow_le_pow_left (two_amgm (a + b) (c + d)) 2
    _ = _ := by ring

private theorem symmetric_extensions {V : Type*} {R : V → V → Prop}
    (hR : ∀ a b, R a b → R b a) (x y : V) :
    extensionsCount R x y = size (fun w => R x w ∧ R y w) ^ 4 := by
  have flip (a b : V) : R a b ↔ R b a := ⟨hR a b, hR b a⟩
  have hy : size (fun w => R x w ∧ R w y) = size (fun w => R x w ∧ R y w) :=
    size_congr (fun w => and_congr Iff.rfl (flip w y))
  have hx : size (fun w => R w x ∧ R y w) = size (fun w => R x w ∧ R y w) :=
    size_congr (fun w => and_congr (flip w x) Iff.rfl)
  have hxy : size (fun w => R w x ∧ R w y) = size (fun w => R x w ∧ R y w) :=
    size_congr (fun w => and_congr (flip w x) (flip w y))
  rw [extensionsCount, hx, hy, hxy]
  ring

private theorem extensions_bound {V : Type*} [Fintype V] {G : Digraph V}
    (hG : Oriented G) (x y : V) :
    2 ^ 8 * extensionsCount G.Adj x y ≤ extensionsCount G.toSimpleGraphInclusive.Adj x y := by
  rw [symmetric_extensions (fun _ _ => SimpleGraph.Adj.symm),
    common_neighbors_partition hG, extensionsCount]
  exact four_amgm _ _ _ _

private theorem leaves_bound {V : Type*} [Fintype V] {G : Digraph V}
    (hG : Oriented G) (x : V) :
    4 * leafCount G.Adj x ≤ leafCount G.toSimpleGraphInclusive.Adj x := by
  have hsymm : size (G.toSimpleGraphInclusive.Adj · x) =
      size (G.toSimpleGraphInclusive.Adj x) :=
    size_congr (fun w => ⟨SimpleGraph.Adj.symm, SimpleGraph.Adj.symm⟩)
  have hdegree : size (G.toSimpleGraphInclusive.Adj x) = size (G.Adj x) + size (G.Adj · x) := by
    simp only [size_eq_sum, indicator_underlying hG, Finset.sum_add_distrib]
  rw [leafCount, leafCount, hsymm, hdegree, ← pow_two, mul_comm (size (G.Adj · x))]
  exact two_amgm _ _

/-- The two identical extension factors let us exchange the images of vertices 1 and 2. -/
private theorem middle_symmetrize {V : Type*} [Fintype V] {G : Digraph V}
    (hG : Oriented G) (x : V) :
    2 * middleCount G.Adj x =
      ∑ y, ∑ z, indicator (G.toSimpleGraphInclusive.Adj y z) *
        extensionsCount G.Adj x y * extensionsCount G.Adj x z := by
  have swap :
      (∑ y, ∑ z, indicator (G.Adj z y) * extensionsCount G.Adj x y * extensionsCount G.Adj x z) =
        middleCount G.Adj x := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => by ac_rfl))
  simp only [indicator_underlying hG, add_mul, Finset.sum_add_distrib, swap, two_mul]
  rfl

private theorem middle_bound {V : Type*} [Fintype V] {G : Digraph V}
    (hG : Oriented G) (x : V) :
    2 ^ 17 * middleCount G.Adj x ≤ middleCount G.toSimpleGraphInclusive.Adj x := by
  calc
    _ = 2 ^ 16 * (2 * middleCount G.Adj x) := by ring
    _ = 2 ^ 16 * (∑ y, ∑ z, indicator (G.toSimpleGraphInclusive.Adj y z) *
        extensionsCount G.Adj x y * extensionsCount G.Adj x z) := by rw [middle_symmetrize hG]
    _ ≤ _ := by
      simp only [middleCount, Finset.mul_sum]
      refine Finset.sum_le_sum (fun y _ => Finset.sum_le_sum (fun z _ => ?_))
      calc
        _ = indicator (G.toSimpleGraphInclusive.Adj y z) *
            (2 ^ 8 * extensionsCount G.Adj x y) * (2 ^ 8 * extensionsCount G.Adj x z) := by ring
        _ ≤ _ := Nat.mul_le_mul
          (Nat.mul_le_mul_left _ (extensions_bound hG x y)) (extensions_bound hG x z)

/-- On `Fin`-labelled carriers, the undirected count is the repository's existing `homCount`.
    The choice of finite labelling is arbitrary. -/
private theorem witness_bound_relabelled {V : Type*} [Fintype V] {n : ℕ} (G : Digraph V)
    (hG : Oriented G) (e : V ≃ Fin n) :
    2 ^ 19 * directedHomCount witness G ≤
      homCount witness.toSimpleGraphInclusive (G.toSimpleGraphInclusive.comap e.symm) := by
  rw [homCount_relabel_host, directed_count_eq_sum, undirected_count_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  calc
    _ = (2 ^ 17 * middleCount G.Adj x) * (4 * leafCount G.Adj x) := by ring
    _ ≤ _ := Nat.mul_le_mul (middle_bound hG x) (leaves_bound hG x)

/-- The inequality holds for every finite oriented host and counts all vertex maps
    that preserve adjacency. -/
private theorem witness_bound {V : Type*} [Finite V] (G : Digraph V) (hG : Oriented G) :
    2 ^ 19 * directedHomCount witness G ≤
      Nat.card {f : Fin 13 → V // ∀ u v, witness.toSimpleGraphInclusive.Adj u v →
        G.toSimpleGraphInclusive.Adj (f u) (f v)} := by
  let _ := Fintype.ofFinite V
  let e := Fintype.equivFin V
  rw [← homCount_relabel_host _ _ e]
  exact witness_bound_relabelled G hG e

/-- Each underlying edge of an oriented graph has a unique direction. -/
private theorem arcCount_eq_edgeCount {V : Type*} (G : Digraph V) (hG : Oriented G) :
    arcCount G = Nat.card G.toSimpleGraphInclusive.edgeSet := by
  let forget : {p : V × V // G.Adj p.1 p.2} → G.toSimpleGraphInclusive.edgeSet := fun p =>
    ⟨s(p.val.1, p.val.2),
      (SimpleGraph.mem_edgeSet G.toSimpleGraphInclusive).mpr
        ((underlying_adj hG).mpr (Or.inl p.property))⟩
  apply Nat.card_congr (Equiv.ofBijective forget ⟨?_, ?_⟩)
  · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ h
    have hp : s(a, b) = s(c, d) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact (hG _ _ hab hcd).elim
  · rintro ⟨e, he⟩
    obtain ⟨⟨a, b⟩, rfl⟩ := Sym2.mk_surjective e
    have hadj := (SimpleGraph.mem_edgeSet G.toSimpleGraphInclusive).mp he
    rcases (underlying_adj hG).mp hadj with hab | hba
    · exact ⟨⟨(a, b), hab⟩, rfl⟩
    · exact ⟨⟨(b, a), hba⟩, Subtype.ext Sym2.eq_swap⟩

/-- Definition 1.2 of arXiv:2611.23222v1, expressed over the rationals. -/
def RelativelyAntiSidorenko {n : ℕ} (D : Digraph (Fin n)) : Prop :=
  ∀ (V : Type*) [Finite V] (G : Digraph V), Oriented G →
    (directedHomCount D G : ℚ) ≤ (1 / 2 : ℚ) ^ Nat.card D.toSimpleGraphInclusive.edgeSet *
      (Nat.card {f : Fin n → V // ∀ u v, D.toSimpleGraphInclusive.Adj u v →
        G.toSimpleGraphInclusive.Adj (f u) (f v)} : ℚ)

private theorem witness_relativeAntiSidorenko : RelativelyAntiSidorenko witness := by
  intro V _ G hG
  have h := witness_bound G hG
  rw [← witness_arcCount, arcCount_eq_edgeCount witness witness_oriented] at h
  rw [one_div, inv_pow, ← div_eq_inv_mul]
  apply (le_div_iff₀ (by positivity)).mpr
  rw [mul_comm]
  exact_mod_cast h

/-- Question 5.3 of arXiv:2611.23222v1. The proof supplies a pattern on 13
vertices with 19 arcs. -/
theorem question_5_3 :
    ∃ (n : ℕ) (D : Digraph (Fin n)), Oriented D ∧ D.toSimpleGraphInclusive.Connected ∧
      arcCount D % 4 = 3 ∧ RelativelyAntiSidorenko D := by
  refine ⟨13, witness, witness_oriented, witness_connected, ?_, witness_relativeAntiSidorenko⟩
  rw [witness_arcCount]

end

end D5.S3.Combinatorics.ExtremalDensity.RelativeAntiSidorenkoArcCount
