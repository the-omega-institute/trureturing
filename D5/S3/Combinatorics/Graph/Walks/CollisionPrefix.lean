/- GID: D5/S3/Combinatorics/Graph/Walks/CollisionPrefix
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/CollisionPrefix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Fin]
   utility: none
   digest: A directed trail missing one edge has two possible endpoint configurations. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-! Ordered edge sequences, missing-edge classification, and exact collision counts. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.CollisionPrefix

open scoped BigOperators

universe u

/-- A length-k ordered walk in the complete directed graph, with loops. -/
abbrev Walk (V : Type u) (k : ℕ) := Fin (k + 1) → V

/-- Consecutive vertices specify the directed edge, retaining its order. -/
def edge {V : Type u} {k : ℕ} (w : Walk V k) (i : Fin k) : V × V :=
  (w i.castSucc, w i.succ)

/-- Delete only the last edge and its final vertex. -/
def initialWalk {V : Type u} {k : ℕ} (w : Walk V (k + 1)) : Walk V k :=
  fun i => w i.castSucc

/-- The first repeated directed edge is the final edge; every vertex occurs. -/
def Collision {V : Type u} {k : ℕ} (v : V) (w : Walk V (k + 1)) : Prop :=
  w 0 = v ∧ Function.Injective (edge (initialWalk w)) ∧
    edge w (Fin.last k) ∈ Set.range (edge (initialWalk w)) ∧ Function.Surjective w

/-- The source's linearly ordered edge sequences have a distinguished start.
There is one sequence for every compatible edge list, including loops. -/
def OrderedEdges (V : Type u) (v : V) (k : ℕ) :=
  {e : Fin (k + 1) → V × V //
    (e 0).1 = v ∧ ∀ i : Fin k, (e i.castSucc).2 = (e i.succ).1}

noncomputable instance orderedEdgesFintype {V : Type u} [Fintype V] (v : V) (k : ℕ) :
    Fintype (OrderedEdges V v k) := by
  classical
  unfold OrderedEdges
  infer_instance

/-- Convert actual vertex walks to, and reconstruct them from, ordered edges.
The inverse retains the first vertex and each successive edge head. -/
def orderedEdgesEquiv {V : Type u} (v : V) (k : ℕ) :
    {w : Walk V (k + 1) // w 0 = v} ≃ OrderedEdges V v k where
  toFun w := ⟨edge w.1, w.2, fun _ => rfl⟩
  invFun e := ⟨Fin.cons v (fun i => (e.1 i).2), Fin.cons_zero _ _⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact w.2.symm
    · rfl

  right_inv e := by
    apply Subtype.ext
    funext i
    apply Prod.ext
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact e.2.1.symm
      · exact e.2.2 j
    · rfl

/-- The collision conditions stated directly on the source's ordered edges. -/
def SourceCollision {V : Type u} {v : V} {k : ℕ} (e : OrderedEdges V v k) : Prop :=
  Function.Injective (fun i : Fin k => e.1 i.castSucc) ∧
    e.1 (Fin.last k) ∈ Set.range (fun i : Fin k => e.1 i.castSucc) ∧
    ∀ a : V, a = v ∨ ∃ i : Fin (k + 1), (e.1 i).2 = a

private theorem coverage_iff {V : Type u} {k : ℕ} (w : Walk V (k + 1)) :
    Function.Surjective w ↔ ∀ a : V, a = w 0 ∨ ∃ i : Fin (k + 1), (edge w i).2 = a := by
  constructor
  · intro h a
    obtain ⟨i, hi⟩ := h a
    exact Fin.cases (fun hzero => Or.inl hzero.symm)
      (fun j hj => Or.inr ⟨j, hj⟩) i hi
  · intro h a
    rcases h a with ha | ⟨i, hi⟩
    · exact ⟨0, ha.symm⟩
    · exact ⟨i.succ, hi⟩

/-- Exact collision-walk correspondence, including fixed start and coverage.
In particular no quotient by cyclic rotation enters either finite carrier. -/
def sourceCollisionEquiv {V : Type u} (v : V) (k : ℕ) :
    {w : Walk V (k + 1) // Collision v w} ≃
      {e : OrderedEdges V v k // SourceCollision e} where
  toFun w := ⟨orderedEdgesEquiv v k ⟨w.1, w.2.1⟩,
    w.2.2.1, w.2.2.2.1, by
      change ∀ a, a = v ∨ ∃ i, (edge w.1 i).2 = a
      simpa only [w.2.1] using (coverage_iff w.1).mp w.2.2.2.2⟩
  invFun e :=
    let w := (orderedEdgesEquiv v k).symm e.1
    ⟨w.1, w.2, by
      have he : edge w.1 = e.1.1 := congrArg Subtype.val
        ((orderedEdgesEquiv v k).apply_symm_apply e.1)
      have hp : edge (initialWalk w.1) = fun i : Fin k => e.1.1 i.castSucc := by
        funext i
        exact congrFun he i.castSucc
      refine ⟨?_, ?_, ?_⟩
      · simpa only [hp] using e.2.1
      · simpa only [hp, he] using e.2.2.1
      · apply (coverage_iff w.1).mpr
        simpa only [he, w.2] using e.2.2.2⟩
  left_inv w := by
    exact Subtype.ext (congrArg
      (fun p : {u : Walk V (k + 1) // u 0 = v} => p.1)
      ((orderedEdgesEquiv v k).symm_apply_apply ⟨w.1, w.2.1⟩))
  right_inv e := by
    apply Subtype.ext
    exact (orderedEdgesEquiv v k).apply_symm_apply e.1

private def indicator {V : Type u} [DecidableEq V] (a x : V) : ℤ :=
  if a = x then 1 else 0

private theorem telescope {k : ℕ} (f : Fin (k + 1) → ℤ) :
    (∑ i : Fin k, (f i.castSucc - f i.succ)) = f 0 - f (Fin.last k) := by
  have h₁ := Fin.sum_univ_castSucc f
  have h₂ := Fin.sum_univ_succ f
  rw [Finset.sum_sub_distrib]
  linarith

private theorem complete_balance {V : Type u} [Fintype V] [DecidableEq V] (x : V) :
    (∑ e : V × V, (indicator e.1 x - indicator e.2 x)) = 0 := by
  rw [Finset.sum_sub_distrib]
  have h := Equiv.sum_comp (Equiv.prodComm V V) (fun e : V × V => indicator e.1 x)
  exact sub_eq_zero.mpr h.symm

private theorem missing_balance {V : Type u} [Fintype V] [DecidableEq V]
    {k : ℕ} (w : Walk V k) (a b : V) (hinj : Function.Injective (edge w))
    (hmiss : Finset.univ.image (edge w) = Finset.univ.erase (a, b)) (x : V) :
    indicator (w 0) x - indicator (w (Fin.last k)) x = indicator b x - indicator a x := by
  have ht := telescope (fun i => indicator (w i) x)
  have hs : (∑ i : Fin k, (indicator (edge w i).1 x - indicator (edge w i).2 x)) =
      ∑ e ∈ Finset.univ.erase (a, b), (indicator e.1 x - indicator e.2 x) := by
    rw [← hmiss, Finset.sum_image]
    intro i _ j _ hij
    exact hinj hij
  have he := Finset.sum_erase_add (Finset.univ : Finset (V × V))
    (fun e => indicator e.1 x - indicator e.2 x) (Finset.mem_univ (a, b))
  have hz := complete_balance x
  change (∑ i : Fin k, (indicator (edge w i).1 x - indicator (edge w i).2 x)) = _ at ht
  linarith

private theorem balance_cases {V : Type u} [DecidableEq V] (v t a b : V)
    (h : ∀ x, indicator v x - indicator t x = indicator b x - indicator a x) :
    (b = v ∧ t = a) ∨ (a = b ∧ a ≠ v ∧ t = v) := by
  by_cases hab : a = b
  · subst b
    have htv : t = v := by
      by_contra ht
      have := h v
      simp [indicator, ht] at this
    by_cases hav : a = v
    · exact Or.inl ⟨hav, htv.trans hav.symm⟩
    · exact Or.inr ⟨rfl, hav, htv⟩
  · have hb : b = v := by
      by_contra hb
      have := h b
      simp [indicator, hab, Ne.symm hb] at this
      split_ifs at this; omega
    subst b
    have ht : t = a := by
      by_contra ht
      have := h a
      simp [indicator, Ne.symm hab, ht] at this
    exact Or.inl ⟨rfl, ht⟩

private theorem missing_edge {n : ℕ} (hn : 2 ≤ n)
    (w : Walk (Fin n) (n * n - 1)) (hinj : Function.Injective (edge w)) :
    ∃ e : Fin n × Fin n, Finset.univ.image (edge w) = Finset.univ.erase e := by
  let s : Finset (Fin n × Fin n) := Finset.univ.image (edge w)
  have hc : s.card = n * n - 1 := by simp [s, Finset.card_image_of_injective, hinj]
  have hm : ((Finset.univ : Finset (Fin n × Fin n)) \ s).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ s)]
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    rw [hc]
    have : 1 ≤ n * n := by nlinarith
    omega
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hm
  refine ⟨e, ?_⟩
  ext f
  have hf := Finset.ext_iff.mp he f
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton] at hf
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  tauto

private theorem almost_covers {n : ℕ} (hn : 2 ≤ n) {k : ℕ}
    (w : Walk (Fin n) k) (e : Fin n × Fin n)
    (hm : Finset.univ.image (edge w) = Finset.univ.erase e) : Function.Surjective w := by
  intro a
  obtain ⟨b, hb⟩ : ∃ b : Fin n, b ≠ e.2 := by
    have hc : 1 < Fintype.card (Fin n) := by simpa only [Fintype.card_fin] using (show 1 < n by omega)
    obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card hc e.2
    exact ⟨b, hb⟩
  have he : (a, b) ∈ Finset.univ.image (edge w) := by
    rw [hm]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h
    exact hb (congrArg Prod.snd h)
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
  exact ⟨i.castSucc, congrArg Prod.fst hi⟩

/-- Every ordered trail using all but one directed edge covers all vertices.
Its missing edge is either from its endpoint back to its start, or a loop
at another vertex while the trail is closed. -/
theorem prefix_structure {n : ℕ} (hn : 2 ≤ n)
    (w : Walk (Fin n) (n * n - 1)) (hinj : Function.Injective (edge w)) :
    Function.Surjective w ∧ ∃ a b : Fin n,
      Finset.univ.image (edge w) = Finset.univ.erase (a, b) ∧
      ((b = w 0 ∧ w (Fin.last (n * n - 1)) = a) ∨
        (a = b ∧ a ≠ w 0 ∧ w (Fin.last (n * n - 1)) = w 0)) := by
  obtain ⟨⟨a, b⟩, hm⟩ := missing_edge hn w hinj
  exact ⟨almost_covers hn w (a, b) hm, a, b, hm,
    balance_cases _ _ _ _ (missing_balance w a b hinj hm)⟩

/-- Apply the omitted-edge classification to the actual collision initialWalk.
The parameterization by `(n*n-1)+1` equals `n*n` whenever `2 ≤ n`. -/
theorem collision_prefix_structure {n : ℕ} (hn : 2 ≤ n) (v : Fin n)
    (w : Walk (Fin n) ((n * n - 1) + 1)) (h : Collision v w) :
    Function.Surjective (initialWalk w) ∧ ∃ a b : Fin n,
      Finset.univ.image (edge (initialWalk w)) = Finset.univ.erase (a, b) ∧
      ((b = v ∧ initialWalk w (Fin.last (n * n - 1)) = a) ∨
        (a = b ∧ a ≠ v ∧ initialWalk w (Fin.last (n * n - 1)) = v)) := by
  have hs : initialWalk w 0 = v := h.1
  simpa only [hs] using prefix_structure hn (initialWalk w) h.2.1

/-- Full edge coverage records actual directed edges, rather than a count formula. -/
def Euler (n : ℕ) (v : Fin n) :=
  {w : Walk (Fin n) (n * n) // w 0 = v ∧ Function.Bijective (edge w)}

noncomputable instance eulerFintype (n : ℕ) (v : Fin n) : Fintype (Euler n v) := by
  classical
  unfold Euler
  infer_instance

private theorem full_closed {n : ℕ} (v : Fin n) (w : Euler n v) :
    w.1 (Fin.last (n * n)) = v := by
  have ht := telescope (fun i => indicator (w.1 i) v)
  have hs := Equiv.sum_comp (Equiv.ofBijective (edge w.1) w.2.2)
    (fun e : Fin n × Fin n => indicator e.1 v - indicator e.2 v)
  have hz := complete_balance v
  change (∑ i : Fin (n * n), (indicator (w.1 i.castSucc) v - indicator (w.1 i.succ) v)) = _ at hs
  have hh : indicator (w.1 0) v - indicator (w.1 (Fin.last (n * n))) v = 0 := by
    linarith
  by_contra hne
  simp [indicator, w.2.1, hne] at hh

private theorem full_covers {n : ℕ} (v : Fin n) (w : Euler n v) :
    Function.Surjective w.1 := by
  intro a
  obtain ⟨i, hi⟩ := w.2.2.2 (a, a)
  exact ⟨i.castSucc, congrArg Prod.fst hi⟩

private def appendVertex {V : Type u} {k : ℕ} (w : Walk V k) (z : V) : Walk V (k + 1) :=
  Fin.snoc w z

private theorem initial_snoc {V : Type u} {k : ℕ} (w : Walk V k) (z : V) :
    initialWalk (appendVertex w z) = w := by
  funext i
  exact Fin.snoc_castSucc (α := fun _ : Fin (k + 2) => V) z w i

private theorem last_edge_snoc {V : Type u} {k : ℕ} (w : Walk V k) (z : V) :
    edge (appendVertex w z) (Fin.last k) = (w (Fin.last k), z) := by
  change ((appendVertex w z) (Fin.last k).castSucc,
    (appendVertex w z) (Fin.last (k + 1))) = _
  simp only [appendVertex, Fin.snoc_castSucc, Fin.snoc_last]

/-- Delete the final repeated edge, or append one of the n outgoing edges.
This is an equivalence of actual ordered finite carriers. -/
noncomputable def longCollisionEquiv (n : ℕ) (v : Fin n) :
    {w : Walk (Fin n) (n * n + 1) // Collision v w} ≃ Euler n v × Fin n where
  toFun w := (⟨initialWalk w.1, w.2.1,
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨w.2.2.1, by simp⟩⟩, w.1 (Fin.last (n * n + 1)))
  invFun p := ⟨appendVertex p.1.1 p.2, by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change appendVertex p.1.1 p.2 0 = v
      simpa only [appendVertex, Fin.snoc_apply_zero] using p.1.2.1
    · rw [initial_snoc]
      exact p.1.2.2.1
    · rw [initial_snoc, last_edge_snoc, full_closed v p.1]
      exact p.1.2.2.2 (v, p.2)
    · intro a
      obtain ⟨i, hi⟩ := full_covers v p.1 a
      exact ⟨i.castSucc, (Fin.snoc_castSucc (α := fun _ : Fin (n * n + 2) => Fin n) p.2 p.1.1 i).trans hi⟩⟩
  left_inv w := by
    apply Subtype.ext
    exact Fin.snoc_init_self w.1
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact initial_snoc _ _
    · exact Fin.snoc_last (α := fun _ : Fin (n * n + 2) => Fin n) _ _

/-- T(n,k) counts the literal ordered edge sequences of total length k. -/
noncomputable def collisionCount (n : ℕ) (v : Fin n) (k : ℕ) : ℕ := by
  classical
  exact match k with
    | 0 => 0
    | k + 1 => Fintype.card {e : OrderedEdges (Fin n) v k // SourceCollision e}

/-- The number of full ordered Euler walks with this fixed start. -/
noncomputable def eulerCount (n : ℕ) (v : Fin n) : ℕ := by
  classical
  exact Fintype.card (Euler n v)

/-- The denominator count is n times the number of full ordered Euler walks. -/
theorem long_count (n : ℕ) (v : Fin n) :
    collisionCount n v (n * n + 1) = n * eulerCount n v := by
  classical
  change Fintype.card {e : OrderedEdges (Fin n) v (n * n) // SourceCollision e} = _
  calc
    _ = Fintype.card {w : Walk (Fin n) (n * n + 1) // Collision v w} :=
      Fintype.card_congr (sourceCollisionEquiv v (n * n)).symm
    _ = Fintype.card (Euler n v × Fin n) := Fintype.card_congr (longCollisionEquiv n v)
    _ = n * eulerCount n v := by simp [Fintype.card_prod, eulerCount, Nat.mul_comm]

end D5.S3.Combinatorics.Graph.Walks.CollisionPrefix
