/- GID: D5/S3/Combinatorics/Graph/ComponentPacking/IntegerLineComponents
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ComponentPacking/IntegerLineComponents
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Int.Interval]
   utility: none
   digest: Ordered maximal integer-edge intervals with exact edge accounting. -/

module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic

/-! Maximal intervals for the graph containing precisely the specified unit edges. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.ComponentPacking

open scoped BigOperators

/-- Only the edges specified by `E` connect vertices: every intervening unit edge
must be present. In particular adjacent occupied vertices need not be connected. -/
def EdgeConnected (E : Finset ℤ) (x y : ℤ) : Prop :=
  ∀ e : ℤ, min x y ≤ e → e < max x y → e ∈ E

/-- All endpoints of specified edges, together with the distinguished target. -/
def occupiedVertices (E : Finset ℤ) (q : ℤ) : Finset ℤ :=
  insert q (E ∪ E.image (fun e => e + 1))

/-- The graph has exactly the specified edges, including when two occupied
vertices are adjacent across an edge absent from `E`. -/
def specifiedEdgeGraph (E : Finset ℤ) : SimpleGraph ℤ where
  Adj x y := (x ∈ E ∧ y = x + 1) ∨ (y ∈ E ∧ x = y + 1)
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := ⟨by intro x h; rcases h with h | h <;> omega⟩

/-- A maximal interval partition, indexed in the original order by its least vertices.
The half-open intervals partition exactly the specified edges. -/
structure IntegerLineIntervals (E : Finset ℤ) (q : ℤ) where
  roots : Finset ℤ
  right : ℤ → ℤ
  nonempty : ∀ a ∈ roots, a ≤ right a
  separated : ∀ a ∈ roots, ∀ b ∈ roots, a < b → right a < b
  vertices : ∀ v : ℤ, v ∈ occupiedVertices E q ↔ ∃ a ∈ roots, a ≤ v ∧ v ≤ right a
  edges : ∀ e : ℤ, e ∈ E ↔ ∃ a ∈ roots, a ≤ e ∧ e < right a
  component : ∀ a ∈ roots, ∀ v : ℤ,
    (specifiedEdgeGraph E).Reachable a v ↔ a ≤ v ∧ v ≤ right a
  target : ℤ
  target_mem : target ∈ roots
  target_bounds : target ≤ q ∧ q ≤ right target
  detached_positive : ∀ a ∈ roots, a ≠ target → a < right a
  edge_count : (∑ a ∈ roots, (right a - a).toNat) = E.card

private theorem edge_refl (E : Finset ℤ) (x : ℤ) : EdgeConnected E x x := by
  intro e h₁ h₂
  simp only [min_self, max_self] at h₁ h₂
  omega

private theorem edge_symm {E : Finset ℤ} {x y : ℤ}
    (h : EdgeConnected E x y) : EdgeConnected E y x := by
  simpa only [EdgeConnected, min_comm, max_comm] using h

private theorem edge_trans {E : Finset ℤ} {x y z : ℤ}
    (hxy : EdgeConnected E x y) (hyz : EdgeConnected E y z) : EdgeConnected E x z := by
  intro e hlo hhi
  by_cases h : min x y ≤ e ∧ e < max x y
  · exact hxy e h.1 h.2
  · exact hyz e (by omega) (by omega)

private theorem graph_reachable_iff (E : Finset ℤ) (x y : ℤ) :
    (specifiedEdgeGraph E).Reachable x y ↔ EdgeConnected E x y := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact edge_refl E _
    | @cons u v w hadj p ih =>
      have hedge : EdgeConnected E u v := by
        rcases hadj with h | h
        · intro e h₁ h₂
          have : e = u := by omega
          simpa only [this] using h.1
        · intro e h₁ h₂
          have : e = v := by omega
          simpa only [this] using h.1
      exact edge_trans hedge ih
  · have forward (a : ℤ) (n : ℕ) : EdgeConnected E a (a + n) →
        (specifiedEdgeGraph E).Reachable a (a + n) := by
      induction n with
      | zero => intro _; simpa using SimpleGraph.Reachable.refl (G := specifiedEdgeGraph E) a
      | succ n ih =>
        intro h
        have he : a + n ∈ E := h (a + n) (by omega) (by omega)
        have hp : EdgeConnected E a (a + n) := by
          intro e he₁ he₂
          exact h e (by omega) (by omega)
        have hadj : (specifiedEdgeGraph E).Adj (a + n) (a + (n + 1 : ℕ)) :=
          Or.inl ⟨he, by omega⟩
        exact (ih hp).trans hadj.reachable
    intro h
    by_cases hxy : x ≤ y
    · have hy : x + ((y - x).toNat : ℤ) = y := by
        have := Int.toNat_of_nonneg (sub_nonneg.mpr hxy)
        omega
      simpa only [hy] using forward x (y - x).toNat (by simpa only [hy] using h)
    · have hx : y + ((x - y).toNat : ℤ) = x := by
        have := Int.toNat_of_nonneg (show 0 ≤ x - y by omega)
        omega
      have hr := forward y (x - y).toNat (by simpa only [hx] using edge_symm h)
      exact (by simpa only [hx] using hr : (specifiedEdgeGraph E).Reachable y x).symm

private theorem connected_endpoint {E : Finset ℤ} {q x y : ℤ}
    (hx : x ∈ occupiedVertices E q) (h : EdgeConnected E x y) :
    y ∈ occupiedVertices E q := by
  rcases lt_trichotomy x y with hlt | rfl | hlt
  · have he : y - 1 ∈ E := h (y - 1) (by omega) (by omega)
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨y - 1, he, by omega⟩
  · exact hx
  · have he : y ∈ E := h y (by omega) (by omega)
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ he)

private noncomputable def vertexClass (E : Finset ℤ) (q v : ℤ) : Finset ℤ :=
  by
  classical
  exact (occupiedVertices E q).filter (EdgeConnected E v)

private theorem class_nonempty {E : Finset ℤ} {q v : ℤ}
    (hv : v ∈ occupiedVertices E q) : (vertexClass E q v).Nonempty := by
  classical
  exact ⟨v, Finset.mem_filter.mpr ⟨hv, edge_refl E v⟩⟩

private noncomputable def classRoot (E : Finset ℤ) (q v : ℤ) : ℤ :=
  if h : (vertexClass E q v).Nonempty then (vertexClass E q v).min' h else v

private noncomputable def classRight (E : Finset ℤ) (q v : ℤ) : ℤ :=
  if h : (vertexClass E q v).Nonempty then (vertexClass E q v).max' h else v

private theorem root_mem {E : Finset ℤ} {q v : ℤ}
    (hv : v ∈ occupiedVertices E q) : classRoot E q v ∈ vertexClass E q v := by
  classical
  simp only [classRoot, dite_eq_left (class_nonempty hv)]
  exact Finset.min'_mem _ _

private theorem right_mem {E : Finset ℤ} {q v : ℤ}
    (hv : v ∈ occupiedVertices E q) : classRight E q v ∈ vertexClass E q v := by
  classical
  simp only [classRight, dite_eq_left (class_nonempty hv)]
  exact Finset.max'_mem _ _

private theorem root_le {E : Finset ℤ} {q v w : ℤ}
    (hv : v ∈ occupiedVertices E q) (hw : w ∈ vertexClass E q v) :
    classRoot E q v ≤ w := by
  classical
  simp only [classRoot, dite_eq_left (class_nonempty hv)]
  exact Finset.min'_le _ _ hw

private theorem le_right {E : Finset ℤ} {q v w : ℤ}
    (hv : v ∈ occupiedVertices E q) (hw : w ∈ vertexClass E q v) :
    w ≤ classRight E q v := by
  classical
  simp only [classRight, dite_eq_left (class_nonempty hv)]
  exact Finset.le_max' _ _ hw

private theorem class_eq {E : Finset ℤ} {q v w : ℤ}
    (h : EdgeConnected E v w) : vertexClass E q v = vertexClass E q w := by
  classical
  ext z
  simp only [vertexClass, Finset.mem_filter]
  exact and_congr_right fun _ => ⟨fun hz => edge_trans (edge_symm h) hz,
    fun hz => edge_trans h hz⟩

private theorem root_eq {E : Finset ℤ} {q v w : ℤ}
    (h : EdgeConnected E v w) (hv : v ∈ occupiedVertices E q) :
    classRoot E q v = classRoot E q w := by
  have hw := connected_endpoint hv h
  simp only [classRoot, class_eq (q := q) h, dite_eq_left (class_nonempty hw)]

private theorem class_interval {E : Finset ℤ} {q v : ℤ}
    (hv : v ∈ occupiedVertices E q) :
    vertexClass E q v = Finset.Icc (classRoot E q v) (classRight E q v) := by
  classical
  ext w
  constructor
  · intro hw
    exact Finset.mem_Icc.mpr ⟨root_le hv hw, le_right hv hw⟩
  · intro hw
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hw
    have hr := (Finset.mem_filter.mp (root_mem hv)).2
    have ht := (Finset.mem_filter.mp (right_mem hv)).2
    have h : EdgeConnected E v w := by
      intro e he₁ he₂
      by_cases he : min v (classRoot E q v) ≤ e ∧ e < max v (classRoot E q v)
      · exact hr e he.1 he.2
      · exact ht e (by omega) (by omega)
    exact Finset.mem_filter.mpr ⟨connected_endpoint hv h, h⟩

private noncomputable def allRoots (E : Finset ℤ) (q : ℤ) : Finset ℤ :=
  (occupiedVertices E q).image (classRoot E q)

private theorem roots_spec {E : Finset ℤ} {q a : ℤ} (ha : a ∈ allRoots E q) :
    a ∈ occupiedVertices E q ∧ classRoot E q a = a := by
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
  have hr := Finset.mem_filter.mp (root_mem hv)
  exact ⟨hr.1, (root_eq hr.2 hv).symm⟩

/-- Every finite specified edge set has its maximal, ordered interval decomposition;
no decomposition or positivity assumption is supplied by the caller. -/
theorem integer_line_component_intervals (E : Finset ℤ) (q : ℤ) :
    Nonempty (IntegerLineIntervals E q) := by
  classical
  let A := allRoots E q
  let b := classRight E q
  have roots (a : ℤ) (ha : a ∈ A) := roots_spec ha
  have interval (a : ℤ) (ha : a ∈ A) :
      vertexClass E q a = Finset.Icc a (b a) := by
    simpa only [(roots a ha).2] using class_interval (roots a ha).1
  have comp (a : ℤ) (ha : a ∈ A) (v : ℤ) :
      EdgeConnected E a v ↔ a ≤ v ∧ v ≤ b a := by
    rw [← Finset.mem_Icc, ← interval a ha, vertexClass, Finset.mem_filter]
    exact ⟨fun h => ⟨connected_endpoint (roots a ha).1 h, h⟩, And.right⟩
  have nonempty (a : ℤ) (ha : a ∈ A) : a ≤ b a :=
    ((comp a ha a).mp (edge_refl E a)).2
  have separated (a : ℤ) (ha : a ∈ A) (c : ℤ) (hc : c ∈ A) (hac : a < c) :
      b a < c := by
    by_contra hn
    have h := (comp a ha c).mpr ⟨hac.le, by omega⟩
    have he := root_eq (q := q) h (roots a ha).1
    rw [(roots a ha).2, (roots c hc).2] at he
    omega
  have vertices (v : ℤ) :
      v ∈ occupiedVertices E q ↔ ∃ a ∈ A, a ≤ v ∧ v ≤ b a := by
    constructor
    · intro hv
      have ha : classRoot E q v ∈ A := Finset.mem_image.mpr ⟨v, hv, rfl⟩
      refine ⟨_, ha, (comp _ ha v).mp ?_⟩
      exact edge_symm (Finset.mem_filter.mp (root_mem hv)).2
    · rintro ⟨a, ha, hv⟩
      exact connected_endpoint (roots a ha).1 ((comp a ha v).mpr hv)
  have edge_inside (a : ℤ) (ha : a ∈ A) (e : ℤ) (he : a ≤ e ∧ e < b a) : e ∈ E :=
    ((comp a ha (b a)).mpr ⟨nonempty a ha, le_rfl⟩) e (by omega) (by omega)
  have edges (e : ℤ) : e ∈ E ↔ ∃ a ∈ A, a ≤ e ∧ e < b a := by
    constructor
    · intro he
      have hv : e ∈ occupiedVertices E q :=
        Finset.mem_insert_of_mem (Finset.mem_union_left _ he)
      obtain ⟨a, ha, hlo, hhi⟩ := (vertices e).mp hv
      have hstep : EdgeConnected E e (e + 1) := by
        intro z hz₁ hz₂
        have : z = e := by omega
        simpa [this] using he
      have hnext := (comp a ha (e + 1)).mp
        (edge_trans ((comp a ha e).mpr ⟨hlo, hhi⟩) hstep)
      exact ⟨a, ha, hlo, by omega⟩
    · rintro ⟨a, ha, he⟩
      exact edge_inside a ha e he
  have hq : q ∈ occupiedVertices E q := Finset.mem_insert_self _ _
  obtain ⟨t, ht, htq⟩ := (vertices q).mp hq
  have positive (a : ℤ) (ha : a ∈ A) (hne : a ≠ t) : a < b a := by
    by_contra hn
    have hab : b a = a := by have := nonempty a ha; omega
    have hav := (roots a ha).1
    rcases Finset.mem_insert.mp hav with haq | hv
    · have hta : EdgeConnected E t a := by
        simpa only [haq] using (comp t ht q).mpr htq
      have he := root_eq (q := q) hta (roots t ht).1
      rw [(roots t ht).2, (roots a ha).2] at he
      exact hne he.symm
    · rcases Finset.mem_union.mp hv with he | he
      · obtain ⟨c, hc, hlo, hhi⟩ := (edges a).mp he
        have hca := (comp c hc a).mpr ⟨hlo, hhi.le⟩
        have heq := root_eq (q := q) hca (roots c hc).1
        rw [(roots c hc).2, (roots a ha).2] at heq
        subst c
        omega
      · obtain ⟨e, he, hae⟩ := Finset.mem_image.mp he
        obtain ⟨c, hc, hlo, hhi⟩ := (edges e).mp he
        have hca := (comp c hc a).mpr ⟨by omega, by omega⟩
        have heq := root_eq (q := q) hca (roots c hc).1
        rw [(roots c hc).2, (roots a ha).2] at heq
        subst c
        omega
  have union_edges : A.biUnion (fun a => Finset.Ico a (b a)) = E := by
    ext e
    simpa only [Finset.mem_biUnion, Finset.mem_Ico] using (edges e).symm
  have disjoint : Set.PairwiseDisjoint (↑A) (fun a => Finset.Ico a (b a)) := by
    intro a ha c hc hne
    apply Finset.disjoint_left.mpr
    intro e he he'
    obtain ⟨h₁, h₂⟩ := Finset.mem_Ico.mp he
    obtain ⟨h₃, h₄⟩ := Finset.mem_Ico.mp he'
    rcases lt_or_gt_of_ne hne with h | h
    · have := separated a ha c hc h; omega
    · have := separated c hc a ha h; omega
  have count := Finset.card_biUnion disjoint
  rw [union_edges] at count
  simp only [Int.card_Ico] at count
  exact ⟨⟨A, b, nonempty, separated, vertices, edges,
    fun a ha v => (graph_reachable_iff E a v).trans (comp a ha v), t, ht, htq, positive,
    count.symm⟩⟩

#print axioms integer_line_component_intervals

end D5.S3.Combinatorics.Graph.ComponentPacking
