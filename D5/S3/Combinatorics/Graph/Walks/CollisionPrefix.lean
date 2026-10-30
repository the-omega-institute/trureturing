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

private theorem full_closed {n k : ℕ} (v : Fin n) (w : Walk (Fin n) k)
    (hstart : w 0 = v) (hedge : Function.Bijective (edge w)) :
    w (Fin.last k) = v := by
  have ht := telescope (fun i => indicator (w i) v)
  have hs := Equiv.sum_comp (Equiv.ofBijective (edge w) hedge)
    (fun e : Fin n × Fin n => indicator e.1 v - indicator e.2 v)
  have hz := complete_balance v
  change (∑ i : Fin k, (indicator (w i.castSucc) v - indicator (w i.succ) v)) = _ at hs
  have hh : indicator (w 0) v - indicator (w (Fin.last k)) v = 0 := by
    linarith
  by_contra hne
  simp [indicator, hstart, hne] at hh

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
    · rw [initial_snoc, last_edge_snoc, full_closed v p.1.1 p.1.2.1 p.1.2.2]
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

/-- Insert a loop at a specified linear vertex position. The cut is retained. -/
def insertLoop {V : Type u} {k : ℕ} (w : Walk V k) (p : Fin (k + 1)) :
    Walk V (k + 1) :=
  fun j => if h : j.val ≤ p.val then w ⟨j.val, by omega⟩
    else w ⟨j.val - 1, by omega⟩

private theorem insert_loop_edge {V : Type u} {k : ℕ}
    (w : Walk V k) (p : Fin (k + 1)) :
    edge (insertLoop w p) p = (w p, w p) := by
  simp only [edge, insertLoop, Fin.val_castSucc, Fin.val_succ]
  simp only [le_refl, dite_true, Nat.not_succ_le_self, dite_false, Nat.add_sub_cancel]

private theorem insert_loop_other {V : Type u} {k : ℕ}
    (w : Walk V k) (p : Fin (k + 1)) (i : Fin k) :
    edge (insertLoop w p) (p.succAbove i) = edge w i := by
  by_cases h : i.castSucc < p
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    apply Prod.ext
    · simp only [edge, insertLoop, Fin.val_castSucc]
      rw [dif_pos (by simpa only [Fin.lt_def, Fin.val_castSucc] using Nat.le_of_lt h)]
      rfl
    · simp only [edge, insertLoop, Fin.val_castSucc, Fin.val_succ]
      rw [dif_pos (by simp only [Fin.lt_def, Fin.val_castSucc] at h; omega)]
      rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt h)]
    apply Prod.ext
    · simp only [edge, insertLoop, Fin.val_castSucc, Fin.val_succ]
      rw [dif_neg (by simp only [Fin.lt_def, Fin.val_castSucc] at h; omega)]
      simp only [Nat.add_sub_cancel]
      rfl
    · simp only [edge, insertLoop, Fin.val_castSucc, Fin.val_succ]
      rw [dif_neg (by simp only [Fin.lt_def, Fin.val_castSucc] at h; omega)]
      congr 1

private theorem insert_loop_start {V : Type u} {k : ℕ}
    (w : Walk V k) (p : Fin (k + 1)) : insertLoop w p 0 = w 0 := by
  simp [insertLoop]

/-- Remove the head vertex of the edge at the marked position. -/
def removeLoop {V : Type u} {k : ℕ} (w : Walk V (k + 1)) (p : Fin (k + 1)) :
    Walk V k :=
  fun j => if h : j.val ≤ p.val then w ⟨j.val, by omega⟩
    else w ⟨j.val + 1, by omega⟩

private theorem remove_insert_loop {V : Type u} {k : ℕ}
    (w : Walk V k) (p : Fin (k + 1)) : removeLoop (insertLoop w p) p = w := by
  funext j
  by_cases h : j.val ≤ p.val
  · simp only [removeLoop, h, dite_true, insertLoop]
  · have hh : ¬ j.val + 1 ≤ p.val := by omega
    simp only [removeLoop, h, dite_false, insertLoop]
    rw [dif_neg hh]
    rfl

private theorem insert_remove_loop {V : Type u} {k : ℕ}
    (w : Walk V (k + 1)) (p : Fin (k + 1))
    (hp : w p.castSucc = w p.succ) : insertLoop (removeLoop w p) p = w := by
  funext j
  by_cases h : j.val ≤ p.val
  · simp only [insertLoop, h, dite_true, removeLoop]
  · by_cases h' : j.val - 1 ≤ p.val
    · have hj : j.val = p.val + 1 := by omega
      simp only [insertLoop, h, dite_false, removeLoop]
      rw [dif_pos h']
      convert hp using 1 <;> congr 1 <;> apply Fin.ext <;> simp <;> omega
    · simp only [insertLoop, h, dite_false, removeLoop]
      rw [dif_neg h']
      congr 1
      apply Fin.ext
      simp
      omega

private theorem remove_loop_start {V : Type u} {k : ℕ}
    (w : Walk V (k + 1)) (p : Fin (k + 1)) : removeLoop w p 0 = w 0 := by
  simp [removeLoop]

private theorem remove_loop_edge {V : Type u} {k : ℕ}
    (w : Walk V (k + 1)) (p : Fin (k + 1))
    (hp : w p.castSucc = w p.succ) (i : Fin k) :
    edge (removeLoop w p) i = edge w (p.succAbove i) := by
  have hw := congrArg (fun z => edge z (p.succAbove i)) (insert_remove_loop w p hp)
  rw [insert_loop_other] at hw
  exact hw

/-- The actual almost-complete trails omitting the loop at a. -/
def MissingLoop (n : ℕ) (v a : Fin n) :=
  {w : Walk (Fin n) (n * n - 1) // w 0 = v ∧
    Function.Injective (edge w) ∧
    Finset.univ.image (edge w) = Finset.univ.erase (a, a)}

noncomputable instance missingLoopFintype (n : ℕ) (v a : Fin n) :
    Fintype (MissingLoop n v a) := by
  classical
  unfold MissingLoop
  infer_instance

private theorem missing_loop_no_loop {n : ℕ} {v a : Fin n} (w : MissingLoop n v a)
    (i : Fin (n * n - 1)) : edge w.1 i ≠ (a, a) := by
  intro h
  have hm : (a, a) ∈ Finset.univ.image (edge w.1) := Finset.mem_image.mpr ⟨i, by simp, h⟩
  rw [w.2.2.2] at hm
  simpa using hm

/-- A missing-loop trail together with one of its linear cuts at that vertex. -/
def MarkedLoop (n : ℕ) (v a : Fin n) :=
  Σ w : MissingLoop n v a, {p : Fin (n * n - 1 + 1) // w.1 p = a}

noncomputable instance markedLoopFintype (n : ℕ) (v a : Fin n) :
    Fintype (MarkedLoop n v a) := by
  classical
  unfold MarkedLoop
  infer_instance

private theorem insert_loop_bijective {n : ℕ} (hn : 2 ≤ n) {v a : Fin n}
    (w : MissingLoop n v a) (p : Fin (n * n - 1 + 1)) (hp : w.1 p = a) :
    Function.Bijective (edge (insertLoop w.1 p)) := by
  classical
  have hsize : n * n - 1 + 1 = n * n := by
    have : 0 < n * n := by positivity
    omega
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by simp only [Fintype.card_fin, Fintype.card_prod]; exact hsize⟩
  intro i j hij
  induction i using Fin.succAboveCases p with
  | x =>
    induction j using Fin.succAboveCases p with
    | x => rfl
    | p j =>
      rw [insert_loop_edge, insert_loop_other, hp] at hij
      exact False.elim (missing_loop_no_loop w j hij.symm)
  | p i =>
    induction j using Fin.succAboveCases p with
    | x =>
      rw [insert_loop_edge, insert_loop_other, hp] at hij
      exact False.elim (missing_loop_no_loop w i hij)
    | p j =>
      rw [insert_loop_other, insert_loop_other] at hij
      exact congrArg p.succAbove (w.2.2.1 hij)

private theorem missing_loop_closed {n : ℕ} {v a : Fin n} (w : MissingLoop n v a) :
    w.1 (Fin.last (n * n - 1)) = v := by
  have h := balance_cases _ _ a a
    (missing_balance w.1 a a w.2.2.1 w.2.2.2)
  rcases h with ⟨h₁, h₂⟩ | ⟨_, _, h₂⟩
  · exact h₂.trans (h₁.trans w.2.1)
  · exact h₂.trans w.2.1

private theorem loop_cut_card {n : ℕ} {v a : Fin n} (ha : a ≠ v)
    (w : MissingLoop n v a) :
    Fintype.card {p : Fin (n * n - 1 + 1) // w.1 p = a} = n - 1 := by
  classical
  let f : {p : Fin (n * n - 1 + 1) // w.1 p = a} → {z : Fin n // z ≠ a} := fun p => by
    have hp : p.1 ≠ Fin.last (n * n - 1) := by
      intro h
      have := p.2
      rw [h, missing_loop_closed w] at this
      exact ha this.symm
    let i : Fin (n * n - 1) := p.1.castPred hp
    have hi : i.castSucc = p.1 := Fin.castSucc_castPred _ _
    refine ⟨(edge w.1 i).2, ?_⟩
    intro hz
    apply missing_loop_no_loop w i
    exact Prod.ext ((congrArg w.1 hi).trans p.2) hz
  have hf : Function.Bijective f := by
    constructor
    · intro p q h
      apply Subtype.ext
      have hp : p.1 ≠ Fin.last (n * n - 1) := by
        intro hh; exact ha (p.2.symm.trans (hh ▸ missing_loop_closed w))
      have hq : q.1 ≠ Fin.last (n * n - 1) := by
        intro hh; exact ha (q.2.symm.trans (hh ▸ missing_loop_closed w))
      have he : edge w.1 (p.1.castPred hp) = edge w.1 (q.1.castPred hq) := by
        apply Prod.ext
        · simpa only [edge, Fin.castSucc_castPred] using p.2.trans q.2.symm
        · exact congrArg Subtype.val h
      have := congrArg Fin.castSucc (w.2.2.1 he)
      simpa only [Fin.castSucc_castPred] using this
    · intro z
      have hz : (a, z.1) ∈ Finset.univ.image (edge w.1) := by
        rw [w.2.2.2]
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, Prod.mk.injEq,
          true_and]
        exact fun h => z.2 (congrArg Prod.snd h)
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
      refine ⟨⟨i.castSucc, congrArg Prod.fst hi⟩, ?_⟩
      apply Subtype.ext
      simpa only [f, Fin.castPred_castSucc] using congrArg Prod.snd hi
  calc
    _ = Fintype.card {z : Fin n // z ≠ a} := Fintype.card_congr (Equiv.ofBijective f hf)
    _ = n - 1 := by simp

private theorem remove_loop_missing {n : ℕ} {k : ℕ} {v a : Fin n}
    (w : Walk (Fin n) (k + 1)) (hw : w 0 = v)
    (he : Function.Bijective (edge w)) (p : Fin (k + 1))
    (hp : edge w p = (a, a)) :
    (removeLoop w p) 0 = v ∧ Function.Injective (edge (removeLoop w p)) ∧
      Finset.univ.image (edge (removeLoop w p)) = Finset.univ.erase (a, a) := by
  classical
  have hpp : w p.castSucc = w p.succ :=
    (congrArg Prod.fst hp).trans (congrArg Prod.snd hp).symm
  refine ⟨(remove_loop_start w p).trans hw, ?_, ?_⟩
  · intro i j h
    rw [remove_loop_edge w p hpp, remove_loop_edge w p hpp] at h
    exact Fin.succAbove_right_injective (he.1 h)
  · ext e
    simp only [Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · rintro ⟨i, hi⟩ h
      rw [remove_loop_edge w p hpp] at hi
      have := he.1 (hi.trans (h.trans hp.symm))
      exact Fin.succAbove_ne p i this
    · intro h
      obtain ⟨i, hi⟩ := he.2 e
      rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩
      · exact False.elim (h (hi.symm.trans hp))
      · exact ⟨j, (remove_loop_edge w p hpp j).trans hi⟩

/-- Inserting the omitted loop at the retained linear cut recovers an Euler walk. -/
noncomputable def loopInsertionEquiv {n : ℕ} (hn : 2 ≤ n) (v a : Fin n) :
    MarkedLoop n v a ≃ Euler n v := by
  classical
  let E := {w : Walk (Fin n) (n * n - 1 + 1) //
    w 0 = v ∧ Function.Bijective (edge w)}
  let f : MarkedLoop n v a → E := fun x =>
    ⟨insertLoop x.1.1 x.2.1, (insert_loop_start _ _).trans x.1.2.1,
      insert_loop_bijective hn x.1 x.2.1 x.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨w, p, hp⟩ ⟨z, q, hq⟩ h
      have hval : insertLoop w.1 p = insertLoop z.1 q := congrArg Subtype.val h
      have hpq : p = q := by
        apply (insert_loop_bijective hn z q hq).1
        rw [← hval, insert_loop_edge, hp]
        rw [hval, insert_loop_edge, hq]
      subst q
      have hwz : w = z := by
        apply Subtype.ext
        have := congrArg (fun t => removeLoop t p) hval
        simpa only [remove_insert_loop] using this
      subst z
      rfl
    · intro w
      obtain ⟨p, hp⟩ := w.2.2.2 (a, a)
      let z : MissingLoop n v a :=
        ⟨removeLoop w.1 p, remove_loop_missing w.1 w.2.1 w.2.2 p hp⟩
      have hz : z.1 p = a := by
        change removeLoop w.1 p p = a
        simp only [removeLoop, le_refl, dite_true]
        exact congrArg Prod.fst hp
      refine ⟨⟨z, p, hz⟩, ?_⟩
      apply Subtype.ext
      exact insert_remove_loop w.1 p
        ((congrArg Prod.fst hp).trans (congrArg Prod.snd hp).symm)
  refine (Equiv.ofBijective f hf).trans (Equiv.cast ?_)
  have hs : n * n - 1 + 1 = n * n := by
    have : 0 < n * n := by positivity
    omega
  change {w : Walk (Fin n) (n * n - 1 + 1) //
    w 0 = v ∧ Function.Bijective (edge w)} = Euler n v
  rw [hs]
  rfl

/-- At a vertex other than the fixed start there are exactly n-1 insertion cuts. -/
theorem loop_count {n : ℕ} (hn : 2 ≤ n) (v a : Fin n) (ha : a ≠ v) :
    eulerCount n v = (n - 1) * Fintype.card (MissingLoop n v a) := by
  classical
  rw [eulerCount, ← Fintype.card_congr (loopInsertionEquiv hn v a)]
  change Fintype.card (Σ w : MissingLoop n v a,
    {p : Fin (n * n - 1 + 1) // w.1 p = a}) = _
  simp only [Fintype.card_sigma, loop_cut_card ha]
  simp [Nat.mul_comm]

private theorem edge_append {V : Type u} {k : ℕ} (w : Walk V k) (z : V) :
    edge (appendVertex w z) = Fin.snoc (edge w) (w (Fin.last k), z) := by
  funext i
  induction i using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using last_edge_snoc w z
  | cast i =>
    change (edge (initialWalk (appendVertex w z))) i = _
    rw [initial_snoc, Fin.snoc_castSucc]

private theorem initial_image {n k : ℕ} (w : Walk (Fin n) (k + 1))
    (he : Function.Bijective (edge w)) :
    Finset.univ.image (edge (initialWalk w)) = Finset.univ.erase (edge w (Fin.last k)) := by
  classical
  ext e
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
  constructor
  · rintro ⟨i, hi⟩ h
    have hh : edge w i.castSucc = edge w (Fin.last k) := hi.trans h
    have := he.1 hh
    exact Fin.castSucc_ne_last i this
  · intro h
    obtain ⟨i, hi⟩ := he.2 e
    induction i using Fin.lastCases with
    | last => exact False.elim (h hi.symm)
    | cast i => exact ⟨i, hi⟩

private theorem append_missing {n k : ℕ} (w : Walk (Fin n) k) (z : Fin n)
    (hs : k + 1 = n * n) (hi : Function.Injective (edge w))
    (hm : Finset.univ.image (edge w) = Finset.univ.erase (w (Fin.last k), z)) :
    Function.Bijective (edge (appendVertex w z)) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by simpa only [Fintype.card_fin, Fintype.card_prod] using hs⟩
  rw [edge_append]
  apply Fin.snoc_injective_of_injective hi
  rintro ⟨i, he⟩
  have hh := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, he⟩
  rw [hm] at hh
  simpa using hh

/-- Trails whose omitted edge closes their endpoint back to the fixed start. -/
def ReturnTrail (n : ℕ) (v : Fin n) :=
  {w : Walk (Fin n) (n * n - 1) // w 0 = v ∧ Function.Injective (edge w) ∧
    Finset.univ.image (edge w) =
      Finset.univ.erase (w (Fin.last (n * n - 1)), v)}

noncomputable instance returnTrailFintype (n : ℕ) (v : Fin n) :
    Fintype (ReturnTrail n v) := by
  classical
  unfold ReturnTrail
  infer_instance

/-- Appending the unique omitted closing edge is a bijection with Euler walks. -/
noncomputable def returnTrailEquiv {n : ℕ} (hn : 2 ≤ n) (v : Fin n) :
    ReturnTrail n v ≃ Euler n v := by
  classical
  have hs : n * n - 1 + 1 = n * n := by
    have : 0 < n * n := by positivity
    omega
  let E := {w : Walk (Fin n) (n * n - 1 + 1) //
    w 0 = v ∧ Function.Bijective (edge w)}
  let e : ReturnTrail n v ≃ E := {
    toFun := fun w => ⟨appendVertex w.1 v, by
      simpa only [appendVertex, Fin.snoc_apply_zero] using w.2.1,
      append_missing w.1 v hs w.2.2.1 w.2.2.2⟩
    invFun := fun w => ⟨initialWalk w.1, w.2.1,
      w.2.2.1.comp (Fin.castSucc_injective _), by
        have hh := initial_image w.1 w.2.2
        have hc := full_closed v w.1 w.2.1 w.2.2
        have hl : edge w.1 (Fin.last (n * n - 1)) =
            (initialWalk w.1 (Fin.last (n * n - 1)), v) := Prod.ext rfl hc
        rwa [hl] at hh⟩
    left_inv := fun w => Subtype.ext (initial_snoc _ _)
    right_inv := fun w => by
      apply Subtype.ext
      have hc := full_closed v w.1 w.2.1 w.2.2
      change Fin.snoc (initialWalk w.1) v = w.1
      calc
        _ = appendVertex (initialWalk w.1) (w.1 (Fin.last (n * n - 1 + 1))) :=
          congrArg (fun z : Fin n => appendVertex (initialWalk w.1) z) hc.symm
        _ = w.1 := Fin.snoc_init_self w.1 }
  refine e.trans (Equiv.cast ?_)
  change {w : Walk (Fin n) (n * n - 1 + 1) //
    w 0 = v ∧ Function.Bijective (edge w)} = Euler n v
  rw [hs]
  rfl

private theorem collision_append {n : ℕ} (hn : 2 ≤ n) (v : Fin n)
    (w : Walk (Fin n) (n * n - 1)) (z : Fin n) (hs : w 0 = v)
    (hi : Function.Injective (edge w))
    (hr : (w (Fin.last (n * n - 1)), z) ∈ Set.range (edge w)) :
    Collision v (appendVertex w z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [appendVertex, Fin.snoc_apply_zero] using hs
  · rwa [initial_snoc]
  · rwa [initial_snoc, last_edge_snoc]
  · intro a
    obtain ⟨i, hi⟩ := (prefix_structure hn w hi).1 a
    exact ⟨i.castSucc, (Fin.snoc_castSucc
      (α := fun _ : Fin (n * n - 1 + 2) => Fin n) z w i).trans hi⟩

private theorem append_injective {V : Type u} {k : ℕ}
    {w t : Walk V k} {z y : V} (h : appendVertex w z = appendVertex t y) :
    w = t ∧ z = y := by
  constructor
  · simpa only [initial_snoc] using congrArg initialWalk h
  · simpa only [appendVertex, Fin.snoc_last] using
      congrArg (fun s => s (Fin.last (k + 1))) h

private abbrev ShortData (n : ℕ) (v : Fin n) :=
  (ReturnTrail n v × {z : Fin n // z ≠ v}) ⊕
    ((Σ a : {a : Fin n // a ≠ v}, MissingLoop n v a.1) × Fin n)

private noncomputable def shortDataMap {n : ℕ} (hn : 2 ≤ n) (v : Fin n) :
    ShortData n v → {w : Walk (Fin n) (n * n - 1 + 1) // Collision v w}
  | .inl (w, z) => ⟨appendVertex w.1 z.1, collision_append hn v w.1 z.1
      w.2.1 w.2.2.1 (by
        have hh : (w.1 (Fin.last (n * n - 1)), z.1) ∈
            Finset.univ.image (edge w.1) := by
          rw [w.2.2.2]
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          exact fun h => z.2 (congrArg Prod.snd h)
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hh
        exact ⟨i, hi⟩)⟩
  | .inr (⟨a, w⟩, z) => ⟨appendVertex w.1 z, collision_append hn v w.1 z
      w.2.1 w.2.2.1 (by
        have hh : (w.1 (Fin.last (n * n - 1)), z) ∈
            Finset.univ.image (edge w.1) := by
          rw [w.2.2.2, missing_loop_closed w]
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          exact fun h => a.2 (congrArg Prod.fst h).symm
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hh
        exact ⟨i, hi⟩)⟩

private theorem erased_edge_eq {n : ℕ} {e f : Fin n × Fin n}
    (h : Finset.univ.erase e = Finset.univ.erase f) : e = f :=
  (Finset.erase_inj Finset.univ (Finset.mem_univ e)).mp h

/-- The two omitted-edge classes retain every ordered prefix and final choice. -/
private noncomputable def shortDataEquiv {n : ℕ} (hn : 2 ≤ n) (v : Fin n) :
    ShortData n v ≃ {w : Walk (Fin n) (n * n - 1 + 1) // Collision v w} := by
  classical
  apply Equiv.ofBijective (shortDataMap hn v)
  constructor
  · intro x y h
    cases x with
    | inl x =>
      rcases x with ⟨w, z⟩
      cases y with
      | inl y =>
        rcases y with ⟨t, q⟩
        have hh := append_injective (congrArg Subtype.val h)
        exact congrArg Sum.inl (Prod.ext (Subtype.ext hh.1) (Subtype.ext hh.2))
      | inr y =>
        rcases y with ⟨⟨a, t⟩, q⟩
        have hh := append_injective (congrArg Subtype.val h)
        have hmi := congrArg (fun s => Finset.univ.image (edge s)) hh.1
        have hm := w.2.2.2.symm.trans (hmi.trans t.2.2.2)
        have he := erased_edge_eq hm
        exact False.elim (a.2 (congrArg Prod.snd he).symm)
    | inr x =>
      rcases x with ⟨⟨a, w⟩, z⟩
      cases y with
      | inl y =>
        rcases y with ⟨t, q⟩
        have hh := append_injective (congrArg Subtype.val h)
        have hmi := congrArg (fun s => Finset.univ.image (edge s)) hh.1
        have hm := w.2.2.2.symm.trans (hmi.trans t.2.2.2)
        have he := erased_edge_eq hm
        exact False.elim (a.2 (congrArg Prod.snd he))
      | inr y =>
        rcases y with ⟨⟨b, t⟩, q⟩
        have hh := append_injective (congrArg Subtype.val h)
        have hmi := congrArg (fun s => Finset.univ.image (edge s)) hh.1
        have hm := w.2.2.2.symm.trans (hmi.trans t.2.2.2)
        have hab : a = b := Subtype.ext (congrArg Prod.fst (erased_edge_eq hm))
        subst b
        have hwt : w = t := Subtype.ext hh.1
        subst t
        have hzq := hh.2
        subst q
        rfl
  · intro w
    obtain ⟨_, a, b, hm, hc⟩ := collision_prefix_structure hn v w.1 w.2
    let z := w.1 (Fin.last (n * n - 1 + 1))
    have hw : appendVertex (initialWalk w.1) z = w.1 := Fin.snoc_init_self w.1
    rcases hc with ⟨hb, ha⟩ | ⟨hab, hav, hend⟩
    · subst b
      let t : ReturnTrail n v := ⟨initialWalk w.1, w.2.1, w.2.2.1, by
        simpa only [ha] using hm⟩
      have hz : z ≠ v := by
        intro hz
        obtain ⟨i, hi⟩ := w.2.2.2.1
        have hh : (a, v) ∈ Finset.univ.image (edge (initialWalk w.1)) := by
          refine Finset.mem_image.mpr ⟨i, Finset.mem_univ i, ?_⟩
          rw [← hw, last_edge_snoc] at hi
          simpa only [ha, hz, initial_snoc] using hi
        rw [hm] at hh
        simpa using hh
      exact ⟨.inl (t, ⟨z, hz⟩), Subtype.ext hw⟩
    · subst b
      let t : MissingLoop n v a := ⟨initialWalk w.1, w.2.1, w.2.2.1, hm⟩
      exact ⟨.inr (⟨⟨a, hav⟩, t⟩, z), Subtype.ext hw⟩

private theorem missing_loop_sum {n : ℕ} (hn : 2 ≤ n) (v : Fin n) :
    (∑ a : {a : Fin n // a ≠ v}, Fintype.card (MissingLoop n v a.1)) =
      eulerCount n v := by
  classical
  have hmul : (n - 1) *
      (∑ a : {a : Fin n // a ≠ v}, Fintype.card (MissingLoop n v a.1)) =
      (n - 1) * eulerCount n v := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ _a : {a : Fin n // a ≠ v}, eulerCount n v :=
        Finset.sum_congr rfl (fun a _ => (loop_count hn v a.1 a.2).symm)
      _ = _ := by simp [Nat.mul_comm]
  exact Nat.eq_of_mul_eq_mul_left (by omega) hmul

/-- The numerator counts both possible omitted-edge classes on the source carrier. -/
theorem short_count {n : ℕ} (hn : 2 ≤ n) (v : Fin n) :
    collisionCount n v (n * n) = (2 * n - 1) * eulerCount n v := by
  classical
  have hs : n * n - 1 + 1 = n * n := by
    have : 0 < n * n := by positivity
    omega
  have hc : collisionCount n v (n * n) = Fintype.card (ShortData n v) := by
    conv_lhs => rw [← hs]
    change Fintype.card {e : OrderedEdges (Fin n) v (n * n - 1) //
      SourceCollision e} = _
    exact (Fintype.card_congr (sourceCollisionEquiv v (n * n - 1))).symm.trans
      (Fintype.card_congr (shortDataEquiv hn v)).symm
  rw [hc]
  change Fintype.card ((ReturnTrail n v × {z : Fin n // z ≠ v}) ⊕
    ((Σ a : {a : Fin n // a ≠ v}, MissingLoop n v a.1) × Fin n)) = _
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_sigma, Fintype.card_fin]
  rw [Fintype.card_congr (returnTrailEquiv hn v), ← eulerCount]
  have hz : Fintype.card {z : Fin n // z ≠ v} = n - 1 := by simp
  rw [hz, missing_loop_sum hn v]
  have htwo : 2 * n - 1 = (n - 1) + n := by omega
  rw [htwo, Nat.add_mul]
  simp only [Nat.mul_comm]

private abbrev Out {n k : ℕ} (w : Walk (Fin n) k) (a : Fin n) :=
  {i : Fin k // (edge w i).1 = a}

private abbrev Into {n k : ℕ} (w : Walk (Fin n) k) (a : Fin n) :=
  {i : Fin k // (edge w i).2 = a}

private theorem degree_balance {n k : ℕ} (w : Walk (Fin n) k) (a : Fin n) :
    (Fintype.card (Out w a) : ℤ) - Fintype.card (Into w a) =
      indicator (w 0) a - indicator (w (Fin.last k)) a := by
  have h := telescope (fun i => indicator (w i) a)
  rw [Finset.sum_sub_distrib] at h
  change (Fintype.card {i : Fin k // w i.castSucc = a} : ℤ) -
    Fintype.card {i : Fin k // w i.succ = a} = _
  rw [Fintype.card_subtype, Fintype.card_subtype]
  simpa [indicator, Finset.sum_ite] using h

private theorem out_injective {n k : ℕ} (w : Walk (Fin n) k)
    (hi : Function.Injective (edge w)) (a : Fin n) :
    Function.Injective (fun i : Out w a => (edge w i.1).2) := by
  intro i j h
  apply Subtype.ext
  exact hi (Prod.ext (i.2.trans j.2.symm) h)

private theorem into_injective {n k : ℕ} (w : Walk (Fin n) k)
    (hi : Function.Injective (edge w)) (a : Fin n) :
    Function.Injective (fun i : Into w a => (edge w i.1).1) := by
  intro i j h
  apply Subtype.ext
  exact hi (Prod.ext h (i.2.trans j.2.symm))

private def LastExit {n k : ℕ} (v : Fin n) (w : Walk (Fin n) k) : Prop :=
  ∀ a b : Fin n, (a, v) ∈ Set.range (edge w) → (a, b) ∈ Set.range (edge w)

private theorem unused_departure {n k : ℕ} (v : Fin n) (w : Walk (Fin n) k)
    (hs : w 0 = v) (hi : Function.Injective (edge w))
    (hl : LastExit v w) (hk : k < n * n) :
    ∃ z : Fin n, (w (Fin.last k), z) ∉ Set.range (edge w) := by
  classical
  by_contra! hfull
  let t := w (Fin.last k)
  have hout : Function.Surjective (fun i : Out w t => (edge w i.1).2) := by
    intro b
    obtain ⟨i, he⟩ := hfull b
    exact ⟨⟨i, congrArg Prod.fst he⟩, congrArg Prod.snd he⟩
  have hco : Fintype.card (Out w t) = n := by
    simpa only [Fintype.card_fin] using Fintype.card_congr
      (Equiv.ofBijective (fun i : Out w t => (edge w i.1).2)
        ⟨out_injective w hi t, hout⟩)
  have hci : Fintype.card (Into w t) ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _
      (into_injective w hi t)
  have hb := degree_balance w t
  rw [hco, hs] at hb
  by_cases ht : t = v
  · have hcard : Fintype.card (Into w t) = n := by
      have heq : w (Fin.last k) = t := rfl
      simp only [← ht, heq, indicator, if_true] at hb
      change (n : ℤ) - Fintype.card (Into w t) = 1 - 1 at hb
      omega
    have hinto : Function.Surjective (fun i : Into w t => (edge w i.1).1) := by
      apply ((Fintype.bijective_iff_injective_and_card _).mpr
        ⟨into_injective w hi t, by simpa only [Fintype.card_fin] using hcard⟩).2
    have he : Function.Surjective (edge w) := by
      rintro ⟨a, b⟩
      obtain ⟨i, hai⟩ := hinto a
      apply hl a b
      exact ⟨i.1, Prod.ext hai (i.2.trans ht)⟩
    have hc := Fintype.card_congr (Equiv.ofBijective (edge w) ⟨hi, he⟩)
    simp only [Fintype.card_fin, Fintype.card_prod] at hc
    omega
  · have hvt : v ≠ t := Ne.symm ht
    have heq : w (Fin.last k) = t := rfl
    simp only [heq, indicator, hvt, if_false, if_true] at hb
    omega

private theorem last_exit_extension {n k : ℕ} (v : Fin n) (w : Walk (Fin n) k)
    (hs : w 0 = v) (hi : Function.Injective (edge w))
    (hl : LastExit v w) (hk : k < n * n) :
    ∃ z : Fin n, (w (Fin.last k), z) ∉ Set.range (edge w) ∧
      LastExit v (appendVertex w z) := by
  classical
  let t := w (Fin.last k)
  obtain ⟨z, hz, hlast⟩ : ∃ z : Fin n, (t, z) ∉ Set.range (edge w) ∧
      (z = v → ∀ b : Fin n, b ≠ v → (t, b) ∈ Set.range (edge w)) := by
    by_cases h : ∃ z : Fin n, z ≠ v ∧ (t, z) ∉ Set.range (edge w)
    · obtain ⟨z, hne, hz⟩ := h
      exact ⟨z, hz, fun h => False.elim (hne h)⟩
    · obtain ⟨z, hz⟩ := unused_departure v w hs hi hl hk
      refine ⟨z, hz, ?_⟩
      intro _ b hb
      by_contra hmiss
      exact h ⟨b, hb, hmiss⟩
  refine ⟨z, hz, ?_⟩
  intro a b ha
  rw [edge_append, Fin.range_snoc] at ha ⊢
  rcases ha with ha | ha
  · have hat : a = t := congrArg Prod.fst ha
    have hzv : z = v := (congrArg Prod.snd ha).symm
    by_cases hb : b = v
    · exact Or.inl (Prod.ext hat (hb.trans hzv.symm))
    · exact Or.inr (hat.symm ▸ hlast hzv b hb)
  · exact Or.inr (hl a b ha)

/-- Reserving every return-to-start edge as a last exit constructs a full walk. -/
theorem euler_nonempty (n : ℕ) (v : Fin n) : Nonempty (Euler n v) := by
  classical
  have hex : ∀ k : ℕ, k ≤ n * n → ∃ w : Walk (Fin n) k,
      w 0 = v ∧ Function.Injective (edge w) ∧ LastExit v w := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨(fun _ => v), rfl, ?_, ?_⟩
      · exact fun i => Fin.elim0 i
      · intro a b h
        obtain ⟨i, _⟩ := h
        exact Fin.elim0 i
    | succ k ih =>
      intro hk
      obtain ⟨w, hs, hi, hl⟩ := ih (by omega)
      obtain ⟨z, hz, hnew⟩ := last_exit_extension v w hs hi hl (by omega)
      refine ⟨appendVertex w z, ?_, ?_, hnew⟩
      · simpa only [appendVertex, Fin.snoc_apply_zero] using hs
      · rw [edge_append]
        exact Fin.snoc_injective_of_injective hi hz
  obtain ⟨w, hs, hi, _⟩ := hex (n * n) le_rfl
  exact ⟨⟨w, hs, (Fintype.bijective_iff_injective_and_card _).mpr ⟨hi, by simp⟩⟩⟩

/-- The literal source denominator is strictly positive. -/
theorem long_count_positive {n : ℕ} (hn : 2 ≤ n) (v : Fin n) :
    0 < collisionCount n v (n * n + 1) := by
  letI := euler_nonempty n v
  rw [long_count]
  exact Nat.mul_pos (by omega) Fintype.card_pos

/-- The exact universal ratio for ordered looped directed edge-collision walks. -/
theorem collision_ratio {n : ℕ} (hn : 2 ≤ n) (v : Fin n) :
    (collisionCount n v (n * n) : ℚ) / collisionCount n v (n * n + 1) =
      (2 * (n : ℚ) - 1) / n := by
  have he : eulerCount n v ≠ 0 := by
    letI := euler_nonempty n v
    exact Nat.ne_of_gt Fintype.card_pos
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have he0 : (eulerCount n v : ℚ) ≠ 0 := by exact_mod_cast he
  rw [short_count hn v, long_count]
  have hc : ((2 * n - 1 : ℕ) : ℚ) = 2 * (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  push_cast
  rw [hc]
  field_simp

end D5.S3.Combinatorics.Graph.Walks.CollisionPrefix
