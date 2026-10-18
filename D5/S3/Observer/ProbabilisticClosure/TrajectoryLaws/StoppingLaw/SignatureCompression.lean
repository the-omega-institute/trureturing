/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureCompression
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A single bias-independent tree relabeling preserves both phase signatures within a uniform window. -/


import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic
import Mathlib.Order.SuccPred.Relation
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WholeTreeSignature
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SeedLaw

/-! Both phase packings assign one actual address to every potential node before execution. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Classical MeasureTheory
namespace D5.S3.Combinatorics.Graph.ComponentPacking

open scoped BigOperators

/-- Only the edges specified by `E` connect vertices: every intervening unit edge
must be present. In particular adjacent occupied vertices need not be connected. -/
private def EdgeConnected (E : Finset ℤ) (x y : ℤ) : Prop :=
  ∀ e : ℤ, min x y ≤ e → e < max x y → e ∈ E

/-- All endpoints of specified edges, together with the distinguished target. -/
def specifiedOccupiedVertices (E : Finset ℤ) (q : ℤ) : Finset ℤ :=
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
  vertices : ∀ v : ℤ, v ∈ specifiedOccupiedVertices E q ↔ ∃ a ∈ roots, a ≤ v ∧ v ≤ right a
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

private theorem specified_edge_symm {E : Finset ℤ} {x y : ℤ}
    (h : EdgeConnected E x y) : EdgeConnected E y x := by
  simpa only [EdgeConnected, min_comm, max_comm] using h

private theorem specified_edge_trans {E : Finset ℤ} {x y z : ℤ}
    (hxy : EdgeConnected E x y) (hyz : EdgeConnected E y z) : EdgeConnected E x z := by
  intro e hlo hhi
  by_cases h : min x y ≤ e ∧ e < max x y
  · exact hxy e h.1 h.2
  · exact hyz e (by omega) (by omega)

private theorem graph_reachable_iff (E : Finset ℤ) (x y : ℤ) :
    (specifiedEdgeGraph E).Reachable x y ↔ EdgeConnected E x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    let : Std.Refl (EdgeConnected E) := ⟨edge_refl E⟩
    let : IsTrans ℤ (EdgeConnected E) := ⟨fun _ _ _ => specified_edge_trans⟩
    rw [← Relation.reflTransGen_eq_self (r := EdgeConnected E)]
    exact Relation.ReflTransGen.mono (fun a b hab => by
      rcases hab with h | h <;> intro e hlo hhi
      · have : e = a := by omega
        simpa only [this] using h.1
      · have : e = b := by omega
        simpa only [this] using h.1) x y h
  · intro h
    apply reflTransGen_of_succ
    · rintro e ⟨hx, hy⟩
      exact Or.inl ⟨h e (by omega) (by omega), by simp [Order.succ_eq_add_one]⟩
    · rintro e ⟨hy, hx⟩
      exact Or.inr ⟨h e (by omega) (by omega), by simp [Order.succ_eq_add_one]⟩

private theorem connected_endpoint {E : Finset ℤ} {q x y : ℤ}
    (hx : x ∈ specifiedOccupiedVertices E q) (h : EdgeConnected E x y) :
    y ∈ specifiedOccupiedVertices E q := by
  rcases lt_trichotomy x y with hlt | rfl | hlt
  · have he : y - 1 ∈ E := h (y - 1) (by omega) (by omega)
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨y - 1, he, by omega⟩
  · exact hx
  · have he : y ∈ E := h y (by omega) (by omega)
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ he)

private noncomputable def intervalVertexClass (E : Finset ℤ) (q v : ℤ) : Finset ℤ :=
  by
  classical
  exact (specifiedOccupiedVertices E q).filter (EdgeConnected E v)

private theorem class_nonempty {E : Finset ℤ} {q v : ℤ}
    (hv : v ∈ specifiedOccupiedVertices E q) : (intervalVertexClass E q v).Nonempty := by
  classical
  exact ⟨v, Finset.mem_filter.mpr ⟨hv, edge_refl E v⟩⟩

private noncomputable def classRoot (E : Finset ℤ) (q v : ℤ) : ℤ :=
  if h : (intervalVertexClass E q v).Nonempty then (intervalVertexClass E q v).min' h else v

private noncomputable def classRight (E : Finset ℤ) (q v : ℤ) : ℤ :=
  if h : (intervalVertexClass E q v).Nonempty then (intervalVertexClass E q v).max' h else v

private theorem interval_root_mem {E : Finset ℤ} {q v : ℤ}
    (hv : v ∈ specifiedOccupiedVertices E q) : classRoot E q v ∈ intervalVertexClass E q v := by
  classical
  simp only [classRoot, dite_eq_left (class_nonempty hv)]
  exact Finset.min'_mem _ _

private theorem right_mem {E : Finset ℤ} {q v : ℤ}
    (hv : v ∈ specifiedOccupiedVertices E q) : classRight E q v ∈ intervalVertexClass E q v := by
  classical
  simp only [classRight, dite_eq_left (class_nonempty hv)]
  exact Finset.max'_mem _ _

private theorem interval_root_le {E : Finset ℤ} {q v w : ℤ}
    (hv : v ∈ specifiedOccupiedVertices E q) (hw : w ∈ intervalVertexClass E q v) :
    classRoot E q v ≤ w := by
  classical
  simp only [classRoot, dite_eq_left (class_nonempty hv)]
  exact Finset.min'_le _ _ hw

private theorem le_right {E : Finset ℤ} {q v w : ℤ}
    (hv : v ∈ specifiedOccupiedVertices E q) (hw : w ∈ intervalVertexClass E q v) :
    w ≤ classRight E q v := by
  classical
  simp only [classRight, dite_eq_left (class_nonempty hv)]
  exact Finset.le_max' _ _ hw

private theorem interval_class_eq {E : Finset ℤ} {q v w : ℤ}
    (h : EdgeConnected E v w) : intervalVertexClass E q v = intervalVertexClass E q w := by
  classical
  ext z
  simp only [intervalVertexClass, Finset.mem_filter]
  exact and_congr_right fun _ => ⟨fun hz => specified_edge_trans (specified_edge_symm h) hz,
    fun hz => specified_edge_trans h hz⟩

private theorem root_eq {E : Finset ℤ} {q v w : ℤ}
    (h : EdgeConnected E v w) (hv : v ∈ specifiedOccupiedVertices E q) :
    classRoot E q v = classRoot E q w := by
  have hw := connected_endpoint hv h
  simp only [classRoot, interval_class_eq (q := q) h, dite_eq_left (class_nonempty hw)]

private theorem class_interval {E : Finset ℤ} {q v : ℤ}
    (hv : v ∈ specifiedOccupiedVertices E q) :
    intervalVertexClass E q v = Finset.Icc (classRoot E q v) (classRight E q v) := by
  classical
  ext w
  constructor
  · intro hw
    exact Finset.mem_Icc.mpr ⟨interval_root_le hv hw, le_right hv hw⟩
  · intro hw
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hw
    have hr := (Finset.mem_filter.mp (interval_root_mem hv)).2
    have ht := (Finset.mem_filter.mp (right_mem hv)).2
    have h : EdgeConnected E v w := by
      intro e he₁ he₂
      by_cases he : min v (classRoot E q v) ≤ e ∧ e < max v (classRoot E q v)
      · exact hr e he.1 he.2
      · exact ht e (by omega) (by omega)
    exact Finset.mem_filter.mpr ⟨connected_endpoint hv h, h⟩

private noncomputable def allRoots (E : Finset ℤ) (q : ℤ) : Finset ℤ :=
  (specifiedOccupiedVertices E q).image (classRoot E q)

private theorem roots_spec {E : Finset ℤ} {q a : ℤ} (ha : a ∈ allRoots E q) :
    a ∈ specifiedOccupiedVertices E q ∧ classRoot E q a = a := by
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
  have hr := Finset.mem_filter.mp (interval_root_mem hv)
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
      intervalVertexClass E q a = Finset.Icc a (b a) := by
    simpa only [(roots a ha).2] using class_interval (roots a ha).1
  have comp (a : ℤ) (ha : a ∈ A) (v : ℤ) :
      EdgeConnected E a v ↔ a ≤ v ∧ v ≤ b a := by
    rw [← Finset.mem_Icc, ← interval a ha, intervalVertexClass, Finset.mem_filter]
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
      v ∈ specifiedOccupiedVertices E q ↔ ∃ a ∈ A, a ≤ v ∧ v ≤ b a := by
    constructor
    · intro hv
      have ha : classRoot E q v ∈ A := Finset.mem_image.mpr ⟨v, hv, rfl⟩
      refine ⟨_, ha, (comp _ ha v).mp ?_⟩
      exact specified_edge_symm (Finset.mem_filter.mp (interval_root_mem hv)).2
    · rintro ⟨a, ha, hv⟩
      exact connected_endpoint (roots a ha).1 ((comp a ha v).mpr hv)
  have edge_inside (a : ℤ) (ha : a ∈ A) (e : ℤ) (he : a ≤ e ∧ e < b a) : e ∈ E :=
    ((comp a ha (b a)).mpr ⟨nonempty a ha, le_rfl⟩) e (by omega) (by omega)
  have edges (e : ℤ) : e ∈ E ↔ ∃ a ∈ A, a ≤ e ∧ e < b a := by
    constructor
    · intro he
      have hv : e ∈ specifiedOccupiedVertices E q :=
        Finset.mem_insert_of_mem (Finset.mem_union_left _ he)
      obtain ⟨a, ha, hlo, hhi⟩ := (vertices e).mp hv
      have hstep : EdgeConnected E e (e + 1) := by
        intro z hz₁ hz₂
        have : z = e := by omega
        simpa [this] using he
      have hnext := (comp a ha (e + 1)).mp
        (specified_edge_trans ((comp a ha e).mpr ⟨hlo, hhi⟩) hstep)
      exact ⟨a, ha, hlo, by omega⟩
    · rintro ⟨a, ha, he⟩
      exact edge_inside a ha e he
  have hq : q ∈ specifiedOccupiedVertices E q := Finset.mem_insert_self _ _
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


/-- An initial segment in the original order of component minima. -/
def OrderedPrefix (A L : Finset ℤ) : Prop :=
  L ⊆ A ∧ ∀ a ∈ L, ∀ b ∈ A, b < a → b ∈ L

/-- Small families go entirely right; otherwise use the shortest prefix whose
vertex sum reaches the number of detached components minus one. -/
def ShortestPrefix (A : Finset ℤ) (size : ℤ → ℤ) (L : Finset ℤ) : Prop :=
  OrderedPrefix A L ∧
    (A.card ≤ 1 → L = ∅) ∧
    (2 ≤ A.card → (A.card : ℤ) - 1 ≤ ∑ a ∈ L, size a) ∧
    (2 ≤ A.card → ∀ P : Finset ℤ, OrderedPrefix A P →
      (A.card : ℤ) - 1 ≤ ∑ a ∈ P, size a → L.card ≤ P.card)

private theorem shortest_prefix_split (A : Finset ℤ) (ell : ℤ → ℤ)
    (positive : ∀ a ∈ A, 1 ≤ ell a) :
    ∃ L : Finset ℤ, ShortestPrefix A (fun a => ell a + 1) L ∧
      (∑ a ∈ L, (ell a + 1)) ≤ ∑ a ∈ A, ell a ∧
      (∑ a ∈ A \ L, (ell a + 1)) ≤ (∑ a ∈ A, ell a) + 1 := by
  classical
  let d := ∑ a ∈ A, ell a
  let size := fun a => ell a + 1
  have dnonneg : 0 ≤ d := Finset.sum_nonneg (fun a ha => by have := positive a ha; omega)
  have total : (∑ a ∈ A, size a) = d + A.card := by
    simp [size, d, Finset.sum_add_distrib]
  by_cases small : A.card ≤ 1
  · refine ⟨∅, ⟨⟨by simp, by simp⟩, fun _ => rfl, ?_, ?_⟩, ?_, ?_⟩
    · intro h; omega
    · intro h; omega
    · simpa using dnonneg
    · simpa only [Finset.sdiff_empty] using (show (∑ a ∈ A, size a) ≤ d + 1 by
        rw [total]; omega)
  have large : 2 ≤ A.card := by omega
  have item_bound (a : ℤ) (ha : a ∈ A) : size a + ((A.card : ℤ) - 1) ≤ d + 1 := by
    have lower : (A.card : ℤ) - 1 ≤ ∑ b ∈ A.erase a, ell b := by
      calc
        (A.card : ℤ) - 1 = ∑ _b ∈ A.erase a, (1 : ℤ) := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_erase_of_mem ha]
          have := Finset.card_pos.mpr ⟨a, ha⟩
          omega
        _ ≤ _ := Finset.sum_le_sum (fun b hb => positive b (Finset.mem_of_mem_erase hb))
    have split := Finset.sum_erase_add A ell ha
    change (∑ b ∈ A.erase a, ell b) + ell a = d at split
    dsimp only [size]
    omega
  let candidates := A.powerset.filter (fun L =>
    OrderedPrefix A L ∧ (A.card : ℤ) - 1 ≤ ∑ a ∈ L, size a)
  have feasible : candidates.Nonempty := by
    refine ⟨A, Finset.mem_filter.mpr ⟨by simp, ⟨?_, ?_⟩⟩⟩
    · exact ⟨(fun _ h => h), fun _ _ _ hb _ => hb⟩
    · rw [total]; omega
  obtain ⟨L, hL, minimal⟩ := Finset.exists_min_image candidates Finset.card feasible
  obtain ⟨hprefix, threshold⟩ := (Finset.mem_filter.mp hL).2
  have nonempty : L.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at threshold
    omega
  let a := L.max' nonempty
  have ha : a ∈ L := Finset.max'_mem _ _
  have prevPrefix : OrderedPrefix A (L.erase a) := by
    refine ⟨(Finset.erase_subset _ _).trans hprefix.1, ?_⟩
    intro b hb c hc hcb
    have hba : b ≤ a := Finset.le_max' _ _ (Finset.mem_of_mem_erase hb)
    exact Finset.mem_erase.mpr ⟨by omega,
      hprefix.2 b (Finset.mem_of_mem_erase hb) c hc hcb⟩
  have below : (∑ b ∈ L.erase a, size b) < (A.card : ℤ) - 1 := by
    by_contra h
    have admissible : L.erase a ∈ candidates := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr prevPrefix.1, prevPrefix, by omega⟩
    have := minimal _ admissible
    have := Finset.card_erase_lt_of_mem ha
    omega
  have splitL := Finset.sum_erase_add L size ha
  have bounda := item_bound a (hprefix.1 ha)
  have upper : (∑ a ∈ L, size a) ≤ d := by omega
  have complement := Finset.sum_sdiff hprefix.1 (f := size)
  rw [total] at complement
  refine ⟨L, ⟨hprefix, by omega, fun _ => threshold, ?_⟩, upper, ?_⟩
  · intro _ P hp hsum
    exact minimal P (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hp.1, hp, hsum⟩)
  · change (∑ a ∈ A \ L, size a) ≤ d + 1
    omega

/-- Sum of vertex sizes strictly before the component with minimum `a`. -/
noncomputable def precedingSize (A : Finset ℤ) (size : ℤ → ℤ) (a : ℤ) : ℤ := by
  classical
  exact ∑ b ∈ A.filter (fun b => b < a), size b

private theorem preceding_nonneg (A : Finset ℤ) (size : ℤ → ℤ)
    (hs : ∀ a ∈ A, 0 ≤ size a) (a : ℤ) : 0 ≤ precedingSize A size a := by
  classical
  exact Finset.sum_nonneg (fun b hb => hs b (Finset.mem_filter.mp hb).1)

private theorem preceding_add_le (A : Finset ℤ) (size : ℤ → ℤ)
    (hs : ∀ a ∈ A, 0 ≤ size a) (a : ℤ) (ha : a ∈ A) :
    precedingSize A size a + size a ≤ ∑ b ∈ A, size b := by
  classical
  have hnot : a ∉ A.filter (fun b => b < a) := by simp
  rw [precedingSize, add_comm, ← Finset.sum_insert hnot]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.insert_subset ha (Finset.filter_subset _ _)) (fun b hb _ => hs b hb)

private theorem preceding_strict_step (A : Finset ℤ) (size : ℤ → ℤ)
    (hs : ∀ a ∈ A, 0 ≤ size a) (a : ℤ) (ha : a ∈ A) (b : ℤ) (hab : a < b) :
    precedingSize A size a + size a ≤ precedingSize A size b := by
  classical
  have hnot : a ∉ A.filter (fun c => c < a) := by simp
  have sub : insert a (A.filter (fun c => c < a)) ⊆ A.filter (fun c => c < b) := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact Finset.mem_filter.mpr ⟨ha, hab⟩
    · obtain ⟨hcA, hca⟩ := Finset.mem_filter.mp hc
      exact Finset.mem_filter.mpr ⟨hcA, by omega⟩
  have := Finset.sum_le_sum_of_subset_of_nonneg sub
    (fun c hc _ => hs c (Finset.mem_filter.mp hc).1)
  simpa only [Finset.sum_insert hnot, precedingSize, add_comm] using this

/-- The complete specified construction, including the original-order shortest
prefix, the translation formula, and guarantees on the entire occupied domain. -/
structure CanonicalTargetPacking (E : Finset ℤ) (q : ℤ) where
  intervals : IntegerLineIntervals E q
  left : Finset ℤ
  split : ShortestPrefix (intervals.roots.erase intervals.target)
    (fun a => intervals.right a - a + 1) left
  map : ℤ → ℤ
  formula : ∀ a ∈ intervals.roots, ∀ v : ℤ,
    a ≤ v → v ≤ intervals.right a →
    map v = v + (if a = intervals.target then 0 else
      if a ∈ left then intervals.target - (∑ b ∈ left, (intervals.right b - b + 1)) +
        precedingSize left (fun b => intervals.right b - b + 1) a - a
      else intervals.right intervals.target + 1 +
        precedingSize (intervals.roots.erase intervals.target \ left)
          (fun b => intervals.right b - b + 1) a - a)
  injective : Set.InjOn map (↑(specifiedOccupiedVertices E q))
  fixed_target : ∀ v : ℤ, intervals.target ≤ v →
    v ≤ intervals.right intervals.target → map v = v
  translates : ∀ a ∈ intervals.roots, ∃ c : ℤ,
    ∀ v : ℤ, a ≤ v → v ≤ intervals.right a → map v = v + c
  edge_preserving : ∀ e ∈ E, map (e + 1) = map e + 1
  edge_bounds : ∀ e ∈ E, q - (E.card : ℤ) ≤ map e ∧ map e ≤ q + (E.card : ℤ)

/-- The ordered shortest-prefix construction fixes the whole target component,
is injective on all occupied vertices, and bounds every queried left endpoint. -/
theorem canonical_target_fixed_packing (E : Finset ℤ) (q : ℤ) :
    Nonempty (CanonicalTargetPacking E q) := by
  classical
  let D := Classical.choice (integer_line_component_intervals E q)
  let ell : ℤ → ℤ := fun a => D.right a - a
  let size : ℤ → ℤ := fun a => ell a + 1
  let A := D.roots.erase D.target
  have positive (a : ℤ) (ha : a ∈ A) : 1 ≤ ell a := by
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp ha
    have := D.detached_positive a hmem hne
    dsimp only [ell]
    omega
  obtain ⟨L, hsplit, hx, hy⟩ := shortest_prefix_split A ell positive
  let R := A \ L
  let x := ∑ a ∈ L, size a
  let y := ∑ a ∈ R, size a
  let d := ∑ a ∈ A, ell a
  have subL : L ⊆ A := hsplit.1.1
  have subR : R ⊆ A := Finset.sdiff_subset
  have rootL (a : ℤ) (ha : a ∈ L) : a ∈ D.roots :=
    Finset.mem_of_mem_erase (subL ha)
  have rootR (a : ℤ) (ha : a ∈ R) : a ∈ D.roots :=
    Finset.mem_of_mem_erase (subR ha)
  have size_nonneg (a : ℤ) (ha : a ∈ D.roots) : 0 ≤ size a := by
    have := D.nonempty a ha
    dsimp only [size, ell]
    omega
  have nonnegL (a : ℤ) (ha : a ∈ L) : 0 ≤ size a := size_nonneg a (rootL a ha)
  have nonnegR (a : ℤ) (ha : a ∈ R) : 0 ≤ size a := size_nonneg a (rootR a ha)
  have xnonneg : 0 ≤ x := Finset.sum_nonneg nonnegL
  have ynonneg : 0 ≤ y := Finset.sum_nonneg nonnegR
  have dnonneg : 0 ≤ d := Finset.sum_nonneg (fun a ha => by have := positive a ha; omega)
  have allLen : (∑ a ∈ D.roots, ell a) = (E.card : ℤ) := by
    rw [← D.edge_count, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro a ha
    exact (Int.toNat_of_nonneg (sub_nonneg.mpr (D.nonempty a ha))).symm
  have accounting : d + ell D.target = (E.card : ℤ) := by
    simpa only [allLen] using Finset.sum_erase_add D.roots ell D.target_mem
  have qlo := D.target_bounds.1
  have qhi := D.target_bounds.2
  have lenspec (a : ℤ) : ell a = D.right a - a := rfl
  have unique (a : ℤ) (ha : a ∈ D.roots) (b : ℤ) (hb : b ∈ D.roots)
      (v : ℤ) (hv : a ≤ v ∧ v ≤ D.right a) (hv' : b ≤ v ∧ v ≤ D.right b) : a = b := by
    rcases lt_trichotomy a b with h | h | h
    · have := D.separated a ha b hb h; omega
    · exact h
    · have := D.separated b hb a ha h; omega
  let shift : ℤ → ℤ := fun a => if a = D.target then 0 else
    if a ∈ L then D.target - x + precedingSize L size a - a
    else D.right D.target + 1 + precedingSize R size a - a
  let f : ℤ → ℤ := fun v =>
    ∑ a ∈ D.roots, if a ≤ v ∧ v ≤ D.right a then v + shift a else 0
  have on_interval (a : ℤ) (ha : a ∈ D.roots) (v : ℤ)
      (hv : a ≤ v ∧ v ≤ D.right a) : f v = v + shift a := by
    dsimp only [f]
    rw [Finset.sum_eq_single a]
    · exact ite_eq_left hv
    · intro b hb hne
      apply ite_eq_right
      intro hbv
      exact hne (unique b hb a ha v hbv hv)
    · intro hn
      exact (hn ha).elim
  have target_shift : shift D.target = 0 := by simp [shift]
  have target_fixed (v : ℤ) (hv₁ : D.target ≤ v) (hv₂ : v ≤ D.right D.target) : f v = v := by
    simpa only [target_shift, add_zero] using on_interval _ D.target_mem v ⟨hv₁, hv₂⟩
  have left_shift (a : ℤ) (ha : a ∈ L) :
      shift a = D.target - x + precedingSize L size a - a := by
    have hne := (Finset.mem_erase.mp (subL ha)).1
    simp only [shift, ite_eq_right hne, ite_eq_left ha]
  have right_shift (a : ℤ) (ha : a ∈ R) :
      shift a = D.right D.target + 1 + precedingSize R size a - a := by
    obtain ⟨hA, hnL⟩ := Finset.mem_sdiff.mp ha
    have hne := (Finset.mem_erase.mp hA).1
    simp only [shift, ite_eq_right hne, ite_eq_right hnL]
  have left_range (a : ℤ) (ha : a ∈ L) (v : ℤ)
      (hv : a ≤ v ∧ v ≤ D.right a) : D.target - x ≤ f v ∧ f v < D.target := by
    rw [on_interval a (rootL a ha) v hv, left_shift a ha]
    have hp := preceding_nonneg L size nonnegL a
    have hb := preceding_add_le L size nonnegL a ha
    change precedingSize L size a + (D.right a - a + 1) ≤ x at hb
    omega
  have right_range (a : ℤ) (ha : a ∈ R) (v : ℤ)
      (hv : a ≤ v ∧ v ≤ D.right a) :
      D.right D.target < f v ∧ f v ≤ D.right D.target + y := by
    rw [on_interval a (rootR a ha) v hv, right_shift a ha]
    have hp := preceding_nonneg R size nonnegR a
    have hb := preceding_add_le R size nonnegR a ha
    change precedingSize R size a + (D.right a - a + 1) ≤ y at hb
    omega
  have same_left (a : ℤ) (ha : a ∈ L) (b : ℤ) (hb : b ∈ L) (hab : a < b)
      (v w : ℤ) (hv : a ≤ v ∧ v ≤ D.right a) (hw : b ≤ w ∧ w ≤ D.right b) :
      f v < f w := by
    rw [on_interval a (rootL a ha) v hv, on_interval b (rootL b hb) w hw,
      left_shift a ha, left_shift b hb]
    have h := preceding_strict_step L size nonnegL a ha b hab
    change precedingSize L size a + (D.right a - a + 1) ≤ precedingSize L size b at h
    omega
  have same_right (a : ℤ) (ha : a ∈ R) (b : ℤ) (hb : b ∈ R) (hab : a < b)
      (v w : ℤ) (hv : a ≤ v ∧ v ≤ D.right a) (hw : b ≤ w ∧ w ≤ D.right b) :
      f v < f w := by
    rw [on_interval a (rootR a ha) v hv, on_interval b (rootR b hb) w hw,
      right_shift a ha, right_shift b hb]
    have h := preceding_strict_step R size nonnegR a ha b hab
    change precedingSize R size a + (D.right a - a + 1) ≤ precedingSize R size b at h
    omega
  have category (a : ℤ) (ha : a ∈ D.roots) : a = D.target ∨ a ∈ L ∨ a ∈ R := by
    by_cases ht : a = D.target
    · exact Or.inl ht
    · by_cases hl : a ∈ L
      · exact Or.inr (Or.inl hl)
      · exact Or.inr (Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨ht, ha⟩, hl⟩))
  have disjoint_images (a : ℤ) (ha : a ∈ D.roots) (b : ℤ) (hb : b ∈ D.roots)
      (hne : a ≠ b) (v w : ℤ) (hv : a ≤ v ∧ v ≤ D.right a)
      (hw : b ≤ w ∧ w ≤ D.right b) : f v ≠ f w := by
    rcases category a ha with rfl | hLa | hRa <;>
      rcases category b hb with rfl | hLb | hRb
    · exact (hne rfl).elim
    · rw [target_fixed v hv.1 hv.2]
      have := (left_range b hLb w hw).2
      omega
    · rw [target_fixed v hv.1 hv.2]
      have := (right_range b hRb w hw).1
      omega
    · rw [target_fixed w hw.1 hw.2]
      have := (left_range a hLa v hv).2
      omega
    · rcases lt_or_gt_of_ne hne with h | h
      · exact ne_of_lt (same_left a hLa b hLb h v w hv hw)
      · exact ne_of_gt (same_left b hLb a hLa h w v hw hv)
    · have := (left_range a hLa v hv).2
      have := (right_range b hRb w hw).1
      have := D.nonempty D.target D.target_mem
      omega
    · rw [target_fixed w hw.1 hw.2]
      have := (right_range a hRa v hv).1
      omega
    · have := (right_range a hRa v hv).1
      have := (left_range b hLb w hw).2
      have := D.nonempty D.target D.target_mem
      omega
    · rcases lt_or_gt_of_ne hne with h | h
      · exact ne_of_lt (same_right a hRa b hRb h v w hv hw)
      · exact ne_of_gt (same_right b hRb a hRa h w v hw hv)
  have injective : Set.InjOn f (↑(specifiedOccupiedVertices E q)) := by
    intro v hv w hw heq
    obtain ⟨a, ha, hav⟩ := (D.vertices v).mp hv
    obtain ⟨b, hb, hbw⟩ := (D.vertices w).mp hw
    by_cases hab : a = b
    · subst b
      rw [on_interval a ha v hav, on_interval a ha w hbw] at heq
      omega
    · exact (disjoint_images a ha b hb hab v w hav hbw heq).elim
  have global_range (v : ℤ) (hv : v ∈ specifiedOccupiedVertices E q) :
      q - (E.card : ℤ) ≤ f v ∧ f v ≤ q + (E.card : ℤ) + 1 := by
    obtain ⟨a, ha, hav⟩ := (D.vertices v).mp hv
    have hlen := lenspec D.target
    change x ≤ d at hx
    change y ≤ d + 1 at hy
    rcases category a ha with rfl | hLa | hRa
    · rw [target_fixed v hav.1 hav.2]
      omega
    · have := left_range a hLa v hav
      omega
    · have := right_range a hRa v hav
      omega
  have edge_preserving (e : ℤ) (he : e ∈ E) : f (e + 1) = f e + 1 := by
    obtain ⟨a, ha, hlo, hhi⟩ := (D.edges e).mp he
    rw [on_interval a ha (e + 1) ⟨by omega, by omega⟩,
      on_interval a ha e ⟨hlo, hhi.le⟩]
    omega
  have edge_bounds (e : ℤ) (he : e ∈ E) :
      q - (E.card : ℤ) ≤ f e ∧ f e ≤ q + (E.card : ℤ) := by
    have heV : e ∈ specifiedOccupiedVertices E q :=
      Finset.mem_insert_of_mem (Finset.mem_union_left _ he)
    have he1V : e + 1 ∈ specifiedOccupiedVertices E q := Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩))
    have h₁ := global_range e heV
    have h₂ := global_range (e + 1) he1V
    have h₃ := edge_preserving e he
    exact ⟨h₁.1, by omega⟩
  refine ⟨⟨D, L, hsplit, f, ?_, injective, target_fixed, ?_, edge_preserving, edge_bounds⟩⟩
  · intro a ha v hv₁ hv₂
    exact on_interval a ha v ⟨hv₁, hv₂⟩
  · intro a ha
    exact ⟨shift a, fun v hv₁ hv₂ => on_interval a ha v ⟨hv₁, hv₂⟩⟩

#print axioms canonical_target_fixed_packing

end D5.S3.Combinatorics.Graph.ComponentPacking

open D5.S3.Combinatorics.Graph.ComponentPacking

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

private def addressParity (t : ℤ) : Bool := decide (t % 2 = 1)

private theorem parity_value (t : ℤ) : (addressParity t).toInt = t % 2 := by
  have hlo := Int.emod_nonneg t (by decide : (2 : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos t (by decide : (0 : ℤ) < 2)
  by_cases h : t % 2 = 1 <;> simp [addressParity, h] <;> omega

private theorem parity_of_active (t : ℤ) (φ : Bool)
    (active : (t - φ.toInt) % 2 = 0) : addressParity t = φ := by
  cases φ
  · change (t - 0) % 2 = 0 at active
    have ht : t % 2 = 0 := by omega
    simp [addressParity, ht]
  · change (t - 1) % 2 = 0 at active
    have ht : t % 2 = 1 := by omega
    simp [addressParity, ht]

private def phaseEdges (T : ReadTree) (φ : Bool) : Finset ℤ :=
  (T.addresses.filter (fun t => addressParity t = φ)).image (fun t => (t - φ.toInt) / 2)

private def phasePacking (j : Bool) (T : ReadTree) (φ : Bool) :
    CanonicalTargetPacking (phaseEdges T φ) (targetIndex j φ) :=
  Classical.choice (canonical_target_fixed_packing (phaseEdges T φ) (targetIndex j φ))

private def compressedAddress (j : Bool) (T : ReadTree) (t : ℤ) : ℤ :=
  2 * (phasePacking j T (addressParity t)).map ((t - (addressParity t).toInt) / 2) +
    (addressParity t).toInt

/-- This map has no bias parameter and produces a single actual integer tree. -/
def compressedTree (j : Bool) (T : ReadTree) : ReadTree := T.relabelPotentialAddresses (compressedAddress j T)

private theorem packed_target (j : Bool) (T : ReadTree) (φ : Bool) :
    (phasePacking j T φ).map (targetIndex j φ) = targetIndex j φ :=
  (phasePacking j T φ).fixed_target _
    (phasePacking j T φ).intervals.target_bounds.1
    (phasePacking j T φ).intervals.target_bounds.2

private theorem compressed_parity (j : Bool) (T : ReadTree) (t : ℤ) :
    compressedAddress j T t % 2 = t % 2 := by
  have hp := parity_value t
  unfold compressedAddress
  omega

private theorem phase_edge_mem (T : ReadTree) (t : ℤ) (ht : t ∈ T.addresses) :
    (t - (addressParity t).toInt) / 2 ∈ phaseEdges T (addressParity t) :=
  Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, rfl⟩, rfl⟩

private theorem slot_in_occupied (j φ : Bool) (T : ReadTree) (s : OrientedSlot) :
    signatureSlotIndex j φ T s ∈ specifiedOccupiedVertices (phaseEdges T φ) (targetIndex j φ) := by
  cases s with
  | none => exact Finset.mem_insert_self _ _
  | some ps =>
    obtain ⟨p, side⟩ := ps
    cases ht : T.addressAt p with
    | none =>
      simpa only [signatureSlotIndex, ht, specifiedOccupiedVertices] using
        (Finset.mem_insert_self (targetIndex j φ)
          (phaseEdges T φ ∪ (phaseEdges T φ).image (fun e => e + 1)))
    | some t =>
      by_cases active : (t - φ.toInt) % 2 = 0
      · have hp : addressParity t = φ := parity_of_active t φ active
        have he : (t - φ.toInt) / 2 ∈ phaseEdges T φ := by
          simpa only [hp] using phase_edge_mem T t (T.addressAt_in_addresses p t ht)
        cases side
        · simpa only [signatureSlotIndex, ht, specifiedOccupiedVertices, ite_eq_left active,
            Bool.toInt_false, add_zero] using
            Finset.mem_insert_of_mem (Finset.mem_union_left
              ((phaseEdges T φ).image (fun e => e + 1)) he)
        · simpa only [signatureSlotIndex, ht, specifiedOccupiedVertices, ite_eq_left active, Bool.toInt_true] using
            Finset.mem_insert_of_mem (Finset.mem_union_right (phaseEdges T φ)
              (Finset.mem_image.mpr ⟨(t - φ.toInt) / 2, he, rfl⟩))
      · simpa only [signatureSlotIndex, ht, specifiedOccupiedVertices, ite_eq_right active] using
          (Finset.mem_insert_self (targetIndex j φ)
            (phaseEdges T φ ∪ (phaseEdges T φ).image (fun e => e + 1)))

private theorem packed_slot (j φ : Bool) (T : ReadTree) (s : OrientedSlot) :
    (phasePacking j T φ).map (signatureSlotIndex j φ T s) = signatureSlotIndex j φ (compressedTree j T) s := by
  cases s with
  | none => exact packed_target j T φ
  | some ps =>
    obtain ⟨p, side⟩ := ps
    have hr := ReadTree.addressAt_relabel (compressedAddress j T) T p
    change (compressedTree j T).addressAt p = (T.addressAt p).map (compressedAddress j T) at hr
    cases ht : T.addressAt p with
    | none =>
      simp only [ht, Option.map_none] at hr
      simpa only [signatureSlotIndex, ht, hr] using packed_target j T φ
    | some t =>
      simp only [ht, Option.map_some] at hr
      have hpar := compressed_parity j T t
      by_cases active : (t - φ.toInt) % 2 = 0
      · have hp : addressParity t = φ := parity_of_active t φ active
        have new_active : (compressedAddress j T t - φ.toInt) % 2 = 0 := by
          unfold compressedAddress
          rw [hp]
          omega
        have edge_pres := (phasePacking j T φ).edge_preserving _
          (by simpa only [hp] using phase_edge_mem T t (T.addressAt_in_addresses p t ht))
        have half : (compressedAddress j T t - φ.toInt) / 2 =
            (phasePacking j T φ).map ((t - φ.toInt) / 2) := by
          unfold compressedAddress
          rw [hp]
          omega
        cases side <;> simp only [signatureSlotIndex, ht, hr, ite_eq_left active,
          ite_eq_left new_active, Bool.toInt_false, Bool.toInt_true, add_zero, half, edge_pres]
      · have new_inactive : (compressedAddress j T t - φ.toInt) % 2 ≠ 0 := by omega
        simpa only [signatureSlotIndex, ht, hr, ite_eq_right active, ite_eq_right new_inactive]
          using packed_target j T φ

/-- The same bias-independent tree preserves both complete signatures and every
formal height, and all its potential addresses lie in the stated uniform window. -/
theorem bounded_signature_relabeling (j : Bool) (T : ReadTree) (k : ℕ)
    (hk : T.height ≤ k) :
    SameSignature j T (compressedTree j T) ∧ (compressedTree j T).height = T.height ∧
      ∀ t ∈ (compressedTree j T).addresses,
        j.toInt - 2 * ((2 ^ k - 1 : ℕ) : ℤ) ≤ t ∧
          t ≤ j.toInt + 2 * ((2 ^ k - 1 : ℕ) : ℤ) + 1 := by
  have same : SameSignature j T (compressedTree j T) := by
    refine ⟨(T.skeleton_relabel _ (fun t _ => compressed_parity j T t)).symm, ?_⟩
    intro φ a b
    rw [← packed_slot j φ T a, ← packed_slot j φ T b]
    exact ⟨congrArg (phasePacking j T φ).map, fun h =>
      (phasePacking j T φ).injective (slot_in_occupied j φ T a)
        (slot_in_occupied j φ T b) h⟩
  refine ⟨same, ReadTree.relabel_height _ T, ?_⟩
  intro t ht
  rw [compressedTree, ReadTree.relabel_addresses] at ht
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
  let φ := addressParity a
  have he := phase_edge_mem T a ha
  have hb := (phasePacking j T φ).edge_bounds _ he
  have hm : (phaseEdges T φ).card ≤ 2 ^ k - 1 := by
    have h₁ := Finset.card_image_le (s := T.addresses.filter (fun t => addressParity t = φ))
      (f := fun t => (t - φ.toInt) / 2)
    have h₂ := Finset.card_filter_le T.addresses (fun t => addressParity t = φ)
    have h₃ := T.addresses_card_le_readCount
    have h₄ := T.readCount_height_bound
    have h₅ := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hk
    change (phaseEdges T φ).card ≤ (T.addresses.filter (fun t => addressParity t = φ)).card at h₁
    omega
  have base : 2 * targetIndex j φ + φ.toInt = j.toInt ∨
      2 * targetIndex j φ + φ.toInt = j.toInt + 1 := by
    cases j <;> cases φ <;> norm_num [targetIndex]
  change j.toInt - 2 * ((2 ^ k - 1 : ℕ) : ℤ) ≤
      2 * (phasePacking j T φ).map ((a - φ.toInt) / 2) + φ.toInt ∧
    2 * (phasePacking j T φ).map ((a - φ.toInt) / 2) + φ.toInt ≤
      j.toInt + 2 * ((2 ^ k - 1 : ℕ) : ℤ) + 1
  dsimp only [φ] at *
  omega

#print axioms bounded_signature_relabeling

private theorem selector_signature_law {U : Type*} [MeasurableSpace U]
    (β : Bias) (j : Bool) (ν : Measure U) [IsProbabilityMeasure ν]
    (T S : U → ReadTree) (hT : Measurable T) (hS : Measurable S)
    (h : ∀ u, SameSignature j (T u) (S u)) :
    ((sourceLaw β).prod ν).map (selectorJoint j T) =
      ((sourceLaw β).prod ν).map (selectorJoint j S) := by
  ext B hB
  rw [Measure.map_apply (measurable_selectorJoint j T hT) hB,
    Measure.map_apply (measurable_selectorJoint j S hS) hB,
    Measure.prod_apply_symm ((measurable_selectorJoint j T hT) hB),
    Measure.prod_apply_symm ((measurable_selectorJoint j S hS) hB)]
  apply lintegral_congr
  intro u
  have hBu : MeasurableSet ((Prod.mk u) ⁻¹' B) :=
    (measurable_const.prodMk measurable_id) hB
  have he := congrArg (fun μ : Measure Observation => μ ((Prod.mk u) ⁻¹' B))
    (same_signature_observation_law j (T u) (S u) (h u) β)
  simpa only [Measure.map_apply (measurable_observation j (T u)) hBu,
    Measure.map_apply (measurable_observation j (S u)) hBu, selectorJoint,
    Set.preimage_preimage, Function.comp_def] using he

/-- Formal address bounds control every actual prefix, including nonreturns. -/
theorem normalized_actual_radius {U : Type*} [MeasurableSpace U]
    (R : RawRule U) (k : ℕ) (hc : R.TotalCap k) (j : Bool) (ρ : ℕ)
    (hb : ∀ u : U, ∀ t ∈ (R.normalize k u).addresses, |t - j.toInt| ≤ (ρ : ℤ)) :
    R.WithinActualRadius j ρ := by
  intro φ S u n r hr a ha
  have hv := (R.normalization_pointwise k hc φ S u).1
  have hmem := R.completes_record_subset u (visible φ S) hv hr a ha
  exact hb u a.1 ((R.normalize k u).record_addresses (visible φ S) a hmem)

/-- Arbitrary completed input rules have representatives on the unchanged seed
space. Full joint law, nonreturn payment and all formal address bounds are retained. -/
private theorem compress_completed_rule {U : Type*} [MeasurableSpace U]
    (ν : Measure U) [IsProbabilityMeasure ν] (β : Bias) (j : Bool) (k : ℕ)
    (Q : CompletedRule U) (hQ : Q.Lawful ((sourceLaw β).prod ν)) (hc : Q.TotalCap k) :
    ∃ R : RawRule U, R.Lawful ∧ R.TotalCap k ∧ R.fullLaw β j ν = Q.fullLaw β j ν ∧
      R.WithinActualRadius j (2 ^ (k + 1) - 1) ∧
      (k = 0 → R.WithinActualRadius j 0) ∧
      ∀ u : U, (R.normalize k u).height ≤ k ∧
        ∀ t ∈ (R.normalize k u).addresses,
          j.toInt - 2 * ((2 ^ k - 1 : ℕ) : ℤ) ≤ t ∧
            t ≤ j.toInt + 2 * ((2 ^ k - 1 : ℕ) : ℤ) + 1 := by
  obtain ⟨T, hm, he⟩ := Q.normalization_version ((sourceLaw β).prod ν) hQ k
  let T₀ : U → ReadTree := fun u => (T u).val
  let S : U → ReadTree := fun u => compressedTree j (T₀ u)
  have hT₀ : Measurable T₀ := measurable_subtype_coe.comp hm
  have hS : Measurable S := (measurable_of_countable (compressedTree j)).comp hT₀
  have hcap (u : U) : (S u).height ≤ k := by
    rw [(bounded_signature_relabeling j (T₀ u) k (T u).property).2.1]
    exact (T u).property
  let R := RawRule.realize S
  have hcR : R.TotalCap k := RawRule.realize_cap S k hcap
  have formal (u : U) : (R.normalize k u).height ≤ k ∧
      ∀ t ∈ (R.normalize k u).addresses,
        j.toInt - 2 * ((2 ^ k - 1 : ℕ) : ℤ) ≤ t ∧
          t ≤ j.toInt + 2 * ((2 ^ k - 1 : ℕ) : ℤ) + 1 := by
    change ((RawRule.realize S).normalize k u).height ≤ k ∧ _
    rw [RawRule.normalize_realize S k u (hcap u)]
    exact ⟨hcap u, (bounded_signature_relabeling j (T₀ u) k (T u).property).2.2⟩
  refine ⟨R, RawRule.realize_lawful S hS, hcR, ?_, ?_, ?_, formal⟩
  · have hj : Q.completedJoint j =ᵐ[(sourceLaw β).prod ν] selectorJoint j T₀ := by
      filter_upwards [he] with p hp
      rw [Q.completed_joint_normalize k hc j p, hp]
      rfl
    calc
      R.fullLaw β j ν = ((sourceLaw β).prod ν).map (selectorJoint j S) :=
        RawRule.fullLaw_realize S k hcap β j ν
      _ = ((sourceLaw β).prod ν).map (selectorJoint j T₀) :=
        (selector_signature_law β j ν T₀ S hT₀ hS
          (fun u => (bounded_signature_relabeling j (T₀ u) k (T u).property).1)).symm
      _ = Q.fullLaw β j ν := (Measure.map_congr hj).symm
  · apply normalized_actual_radius R k hcR j
    intro u t ht
    have hb := (formal u).2 t ht
    have hp : 0 < 2 ^ k := pow_pos (by decide) _
    have heq : 2 * (2 ^ k - 1) + 1 = 2 ^ (k + 1) - 1 := by rw [pow_succ]; omega
    rw [← heq]
    push_cast
    exact abs_le.mpr ⟨by omega, by omega⟩
  · intro hk
    apply normalized_actual_radius R k hcR j
    intro u t ht
    have hh := (formal u).1
    cases htree : R.normalize k u with
    | leaf a => simp [htree, ReadTree.addresses] at ht
    | read a z o => simp only [htree, ReadTree.height] at hh; omega

/-- The comparison class fixes the entire seed space and full joint law, while
allowing different adaptive rules and imposing only an actual address radius. -/
def UniversalRadius {U : Type*} [MeasurableSpace U]
    (β : Bias) (j : Bool) (ν : Measure U) (k ρ : ℕ) : Prop :=
  ∀ Q : CompletedRule U, Q.Lawful ((sourceLaw β).prod ν) → Q.TotalCap k →
    ∃ R : CompletedRule U, R.Lawful ((sourceLaw β).prod ν) ∧ R.TotalCap k ∧
      R.fullLaw β j ν = Q.fullLaw β j ν ∧ R.CompletedWithinActualRadius j ρ

private theorem universal_radius_upper {U : Type*} [MeasurableSpace U]
    (β : Bias) (j : Bool) (ν : Measure U) [IsProbabilityMeasure ν] (k : ℕ) :
    UniversalRadius β j ν k (2 ^ (k + 1) - 1) := by
  intro Q hQ hc
  obtain ⟨R, hR, hcap, hlaw, hradius, _⟩ :=
    compress_completed_rule ν β j k Q hQ hc
  refine ⟨CompletedRule.fromRaw R, CompletedRule.fromRaw_lawful R hR _, ?_, hlaw, ?_⟩
  · intro s u
    exact hcap s.1 s.2 u
  · intro s u n r hr a ha
    exact hradius s.1 s.2 u n r hr a ha

private theorem universal_radius_exists {U : Type*} [MeasurableSpace U]
    (β : Bias) (j : Bool) (ν : Measure U) [IsProbabilityMeasure ν] (k : ℕ) :
    ∃ ρ : ℕ, UniversalRadius β j ν k ρ := ⟨_, universal_radius_upper β j ν k⟩

/-- A least natural radius is taken only after uniform nonemptiness is proved. -/
def rhoLaw {U : Type*} [MeasurableSpace U]
    (β : Bias) (j : Bool) (ν : Measure U) [IsProbabilityMeasure ν] (k : ℕ) : ℕ :=
  Nat.find (universal_radius_exists β j ν k)

private theorem universal_radius_lower {U : Type*} [MeasurableSpace U]
    (β : Bias) (j : Bool) (ν : Measure U) [IsProbabilityMeasure ν]
    (k : ℕ) (hk : 1 ≤ k) (ρ : ℕ) (hρ : UniversalRadius β j ν k ρ) :
    2 * k + 1 ≤ ρ := by
  have hw := CompletedRule.completed_stopping_witness_exact_radius β j k hk ν
  obtain ⟨W, hW, hcW, hlawW, _⟩ := hw.1
  obtain ⟨P, hP, hcP, hlawP, hradiusP⟩ := hρ W hW hcW
  exact hw.2 ⟨P, hP, hcP, hlawP.trans hlawW, hradiusP⟩

/-- Uniform compression uses the original seed and actual replies. The same
construction supplies the universal upper bound and the exact small budgets. -/
theorem completed_rule_uniform_compression {U : Type*} [MeasurableSpace U]
    (ν : Measure U) [IsProbabilityMeasure ν] (β : Bias) (j : Bool) (k : ℕ) :
    (∀ Q : CompletedRule U, Q.Lawful ((sourceLaw β).prod ν) → Q.TotalCap k →
      ∃ R : RawRule U, R.Lawful ∧ R.TotalCap k ∧ R.fullLaw β j ν = Q.fullLaw β j ν ∧
      R.WithinActualRadius j (2 ^ (k + 1) - 1) ∧
      (k = 0 → R.WithinActualRadius j 0) ∧
      ∀ u : U, (R.normalize k u).height ≤ k ∧
        ∀ t ∈ (R.normalize k u).addresses,
          j.toInt - 2 * ((2 ^ k - 1 : ℕ) : ℤ) ≤ t ∧
            t ≤ j.toInt + 2 * ((2 ^ k - 1 : ℕ) : ℤ) + 1) ∧
    rhoLaw β j ν 0 = 0 ∧ rhoLaw β j ν 1 = 3 ∧
    (1 ≤ k → 2 * k + 1 ≤ rhoLaw β j ν k) ∧
    rhoLaw β j ν k ≤ 2 ^ (k + 1) - 1 := by
  have zero : UniversalRadius β j ν 0 0 := by
    intro A hA hcA
    obtain ⟨R, hR, hcap, hlaw, _, hzero, _⟩ :=
      compress_completed_rule ν β j 0 A hA hcA
    refine ⟨CompletedRule.fromRaw R, CompletedRule.fromRaw_lawful R hR _, ?_, hlaw, ?_⟩
    · intro s u
      exact hcap s.1 s.2 u
    · intro s u n r hr a ha
      exact hzero rfl s.1 s.2 u n r hr a ha
  have lower (n : ℕ) (hn : 1 ≤ n) : 2 * n + 1 ≤ rhoLaw β j ν n :=
    universal_radius_lower β j ν n hn _ (Nat.find_spec (universal_radius_exists β j ν n))
  have upper (n : ℕ) : rhoLaw β j ν n ≤ 2 ^ (n + 1) - 1 :=
    Nat.find_min' (universal_radius_exists β j ν n) (universal_radius_upper β j ν n)
  refine ⟨(fun Q hQ hc => compress_completed_rule ν β j k Q hQ hc),
    ?_, ?_, lower k, upper k⟩
  · exact Nat.le_zero.mp (Nat.find_min' (universal_radius_exists β j ν 0) zero)
  · have hl := lower 1 (by decide)
    have hu := upper 1
    norm_num at hl hu
    omega

#print axioms completed_rule_uniform_compression

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
