/- GID: D5/S3/Combinatorics/Graph/Paths/AlternatingRank
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Paths/AlternatingRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Rank]
   utility: none
   digest: Alternating edge-subgraph ranks of paths over the binary field. -/

/-
The path difference and its partition separator have proof_shape: content and
admission_basis: escape-witness. The live relation is the alternating rank sum
of all edge subgraphs of one path, used by path_separator and then by
partition_rank_independent. The separator uses the same colour word for every
test partition. All purely algebraic and finite-coordinate helpers are consumed
on this chain; they supply no independent admission basis.
The real coefficient argument does not assert a graph-state realization or an
entropy-weight identity.
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

open scoped BigOperators
open Matrix Module

namespace D5.S3.Combinatorics.Graph.Paths.AlternatingRank

attribute [local instance] Classical.propDecidable

/-- The adjacency matrix of the edge subgraph selected by a Boolean edge word.
The vertices remain distinct even when a later colouring repeats a colour. -/
def adjacency : {n : ℕ} → (Fin n → Bool) → Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)
  | 0, _ => 0
  | _n + 1, w => fun i j =>
      Fin.cases (Fin.cases 0 (fun j => if j = 0 then (if w 0 then 1 else 0) else 0) j)
        (fun i => Fin.cases (if i = 0 then (if w 0 then 1 else 0) else 0)
          (fun j => adjacency (fun k => w k.succ) i j) j) i

private theorem mulVec_zero {n : ℕ} (b : Bool) (w : Fin n → Bool)
    (x : Fin (n + 2) → ZMod 2) :
    (adjacency (Fin.cons b w) *ᵥ x) 0 = (if b then 1 else 0) * x (0 : Fin (n + 1)).succ := by
  simp [adjacency, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem mulVec_succ {n : ℕ} (b : Bool) (w : Fin n → Bool)
    (x : Fin (n + 2) → ZMod 2) (i : Fin (n + 1)) :
    (adjacency (Fin.cons b w) *ᵥ x) i.succ =
      (if i = 0 then (if b then 1 else 0) else 0) * x 0 +
        (adjacency w *ᵥ Fin.tail x) i := by
  simp [adjacency, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.tail]

private theorem rank_false {n : ℕ} (w : Fin n → Bool) :
    (adjacency (Fin.cons false w)).rank = (adjacency w).rank := by
  let e : LinearMap.ker (adjacency (Fin.cons false w)).mulVecLin ≃ₗ[ZMod 2]
      (ZMod 2 × LinearMap.ker (adjacency w).mulVecLin) :=
    { toFun := fun x => (x.1 0, ⟨Fin.tail x.1, by
        change adjacency w *ᵥ Fin.tail x.1 = 0
        funext i
        have h := congrFun x.2 i.succ
        change (adjacency (Fin.cons false w) *ᵥ x.1) i.succ = 0 at h
        simpa only [mulVec_succ, Bool.false_eq_true, ↓reduceIte, ite_self, zero_mul,
          zero_add, Pi.zero_apply] using h⟩)
      invFun := fun y => ⟨Fin.cons y.1 y.2.1, by
        change adjacency (Fin.cons false w) *ᵥ Fin.cons y.1 y.2.1 = 0
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [mulVec_zero]
        · have h := congrFun y.2.2 j
          change (adjacency w *ᵥ y.2.1) j = 0 at h
          simpa only [mulVec_succ, Bool.false_eq_true, ↓reduceIte, zero_mul,
            zero_add, ite_self, Pi.zero_apply, Fin.tail_cons] using h⟩
      left_inv := by intro x; apply Subtype.ext; exact Fin.cons_self_tail _
      right_inv := by intro y; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  have he := e.finrank_eq
  simp only [Module.finrank_prod, Module.finrank_self] at he
  have h₁ := (adjacency (Fin.cons false w)).mulVecLin.finrank_range_add_finrank_ker
  have h₂ := (adjacency w).mulVecLin.finrank_range_add_finrank_ker
  simp only [Module.finrank_pi, Fintype.card_fin] at h₁ h₂
  change (adjacency (Fin.cons false w)).rank + _ = _ at h₁
  change (adjacency w).rank + _ = _ at h₂
  omega

private theorem ker_true_iff {n : ℕ} (b : Bool) (w : Fin n → Bool)
    (x : Fin (n + 3) → ZMod 2) :
    adjacency (Fin.cons true (Fin.cons b w)) *ᵥ x = 0 ↔
      x (0 : Fin (n + 2)).succ = 0 ∧ x 0 = -(if b then 1 else 0) * x (0 : Fin (n + 1)).succ.succ ∧
        adjacency w *ᵥ Fin.tail (Fin.tail x) = 0 := by
  constructor
  · intro h
    have h₀ := congrFun h 0
    have h₁ := congrFun h (0 : Fin (n + 2)).succ
    simp only [mulVec_zero, ↓reduceIte, one_mul, Pi.zero_apply] at h₀
    refine ⟨h₀, ?_, ?_⟩
    · have he : x 0 + (if b then 1 else 0) * x (0 : Fin (n + 1)).succ.succ = 0 := by
        rw [mulVec_succ, mulVec_zero] at h₁
        simpa only [↓reduceIte, one_mul, Fin.tail, Pi.zero_apply] using h₁
      linear_combination he
    · ext i
      have hi := congrFun h i.succ.succ
      simpa only [mulVec_succ, Fin.succ_ne_zero, ↓reduceIte, zero_mul, zero_add,
        Fin.tail, h₀, mul_zero, Pi.zero_apply] using hi
  · rintro ⟨h₀, h₁, ht⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [mulVec_zero, ↓reduceIte, one_mul, Pi.zero_apply] using h₀
    · refine Fin.cases ?_ (fun k => ?_) j
      · rw [mulVec_succ, mulVec_zero]
        simp only [↓reduceIte, one_mul, Fin.tail, h₁, neg_mul, neg_add_cancel,
          Pi.zero_apply]
      · simpa only [mulVec_succ, Fin.succ_ne_zero, ↓reduceIte, zero_mul, zero_add,
          Fin.tail, h₀, mul_zero, Pi.zero_apply] using congrFun ht k

private theorem rank_true {n : ℕ} (b : Bool) (w : Fin n → Bool) :
    (adjacency (Fin.cons true (Fin.cons b w))).rank = (adjacency w).rank + 2 := by
  let e : LinearMap.ker (adjacency (Fin.cons true (Fin.cons b w))).mulVecLin ≃ₗ[ZMod 2]
      LinearMap.ker (adjacency w).mulVecLin :=
    { toFun := fun x => ⟨Fin.tail (Fin.tail x.1), (ker_true_iff b w x.1).1 x.2 |>.2.2⟩
      invFun := fun y => ⟨Fin.cons (-(if b then 1 else 0) * y.1 0)
          (Fin.cons 0 y.1), (ker_true_iff b w _).2 (by
            simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail_cons, true_and]
            exact y.2)⟩
      left_inv := by
        intro x
        apply Subtype.ext
        have hx := (ker_true_iff b w x.1).1 x.2
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa [Fin.tail] using hx.2.1.symm
        · refine Fin.cases ?_ (fun k => ?_) j
          · simpa using hx.1.symm
          · rfl
      right_inv := by intro y; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  have he := e.finrank_eq
  have h₁ := (adjacency (Fin.cons true (Fin.cons b w))).mulVecLin.finrank_range_add_finrank_ker
  have h₂ := (adjacency w).mulVecLin.finrank_range_add_finrank_ker
  simp only [Module.finrank_pi, Fintype.card_fin] at h₁ h₂
  change (adjacency (Fin.cons true (Fin.cons b w))).rank + _ = _ at h₁
  change (adjacency w).rank + _ = _ at h₂
  omega

private theorem rank_single (b : Bool) :
    (adjacency (fun _ : Fin 1 => b)).rank = if b then 2 else 0 := by
  cases b
  · have h : adjacency (fun _ : Fin 1 => false) = 0 := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    simp [h]
  · have h : (adjacency (fun _ : Fin 1 => true)).det ≠ 0 := by
      rw [Matrix.det_fin_two]
      change (0 * 0 - 1 * 1 : ZMod 2) ≠ 0
      decide
    simpa using Matrix.rank_of_det_ne_zero h

private def edgeSign {n : ℕ} (w : Fin n → Bool) : ℤ :=
  ∏ i, if w i then -1 else 1

private theorem edgeSign_cons {n : ℕ} (b : Bool) (w : Fin n → Bool) :
    edgeSign (Fin.cons b w) = (if b then -1 else 1) * edgeSign w := by
  simp only [edgeSign, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

private theorem edgeSign_eq {n : ℕ} (w : Fin n → Bool) :
    edgeSign w = (-1 : ℤ) ^ (Finset.univ.filter (fun i => w i = true)).card := by
  simp [edgeSign, Finset.prod_ite]

private theorem sum_words {n : ℕ} (f : (Fin (n + 1) → Bool) → ℤ) :
    (∑ w, f w) = (∑ w : Fin n → Bool, f (Fin.cons false w)) +
      ∑ w : Fin n → Bool, f (Fin.cons true w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp f,
    Fintype.sum_prod_type, Fintype.sum_bool]
  exact add_comm _ _

/-- The signed sum over all edge choices, with the sign computed in the integers. -/
noncomputable def alternatingRank (n : ℕ) : ℤ :=
  ∑ w : Fin n → Bool, (-1 : ℤ) ^ (Finset.univ.filter (fun i => w i = true)).card *
    (adjacency w).rank

private theorem alternatingRank_as_product (n : ℕ) :
    alternatingRank n = ∑ w : Fin n → Bool, edgeSign w * (adjacency w).rank := by
  simp only [alternatingRank, edgeSign_eq]

private theorem alternatingRank_step (n : ℕ) :
    alternatingRank (n + 2) = alternatingRank (n + 1) := by
  rw [alternatingRank_as_product, sum_words]
  simp only [edgeSign_cons, Bool.false_eq_true, ↓reduceIte,
    one_mul, neg_one_mul, rank_false]
  rw [sum_words (f := fun w : Fin (n + 1) → Bool =>
    -edgeSign w * ((adjacency (Fin.cons true w)).rank : ℤ))]
  simp only [edgeSign_cons, Bool.false_eq_true, ↓reduceIte,
    one_mul, neg_one_mul, rank_true, neg_neg]
  rw [← Finset.sum_add_distrib]
  simp only [neg_mul, neg_add_cancel, Finset.sum_const_zero, add_zero]
  exact (alternatingRank_as_product (n + 1)).symm

/-- Every nonempty path has signed edge-subgraph rank sum minus two.
The exponent is the number of retained edges, and the equality is in the integers. -/
theorem alternating_rank (n : ℕ) (hn : 0 < n) : alternatingRank n = -2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  clear hn
  induction n with
  | zero =>
      have hc (b : Bool) (w : Fin 0 → Bool) : Fin.cons b w = (fun _ : Fin 1 => b) := by
        ext i; fin_cases i; rfl
      rw [alternatingRank_as_product, sum_words]
      simp only [hc, rank_single]
      simp [edgeSign]
  | succ n ih => rw [alternatingRank_step, ih]

private theorem edgeSign_flip {n : ℕ} (w : Fin n → Bool) (i : Fin n) :
    edgeSign (Function.update w i (!w i)) = -edgeSign w := by
  unfold edgeSign
  simp_rw [Function.apply_update (fun (_ : Fin n) (b : Bool) => if b then (-1 : ℤ) else 1)]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ (fun j => if w j then (-1 : ℤ) else 1) (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase]
  cases w i <;> simp

private theorem masked_sum_zero {n : ℕ} (mask : Fin n → Bool)
    (i : Fin n) (hi : mask i = false) (F : (Fin n → Bool) → ℤ) :
    (∑ w : Fin n → Bool, edgeSign w * F (fun j => w j && mask j)) = 0 := by
  apply Finset.sum_ninvolution (fun w => Function.update w i (!w i))
  · intro w
    have he : (fun j => Function.update w i (!w i) j && mask j) =
        (fun j => w j && mask j) := by
      funext j
      by_cases hj : j = i
      · subst j; simp [hi]
      · simp [Function.update_of_ne hj]
    rw [he, edgeSign_flip, neg_mul, add_neg_cancel]
  · intro w _
    simpa only [Function.update_ne_self_iff] using Bool.not_ne_self (w i)
  · intro w; exact Finset.mem_univ _
  · intro w
    simp only [Function.update_self, Bool.not_not, Function.update_idem, Function.update_eq_self]

private theorem masked_alternating_rank {n : ℕ} (hn : 0 < n) (mask : Fin n → Bool) :
    (∑ w : Fin n → Bool, edgeSign w *
      ((adjacency (fun j => w j && mask j)).rank : ℤ)) =
        if ∀ i, mask i = true then -2 else 0 := by
  classical
  by_cases h : ∀ i, mask i = true
  · rw [if_pos h]
    simp only [h, Bool.and_true]
    rw [← alternatingRank_as_product, alternating_rank n hn]
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact masked_sum_zero mask i (Bool.eq_false_iff.mpr hi) (fun w => (adjacency w).rank)

private theorem exists_color_word {α : Type*} [Finite α] (π : Setoid α) (hπ : π ≠ ⊤) :
    ∃ (n : ℕ) (_ : 0 < n) (c : Fin (n + 1) → α),
      (∀ k : Fin n, ¬ π (c k.castSucc) (c k.succ)) ∧
      ∀ x y, ¬ π x y → ∃ k : Fin n,
        (c k.castSucc = x ∧ c k.succ = y) ∨ (c k.castSucc = y ∧ c k.succ = x) := by
  classical
  let := Fintype.ofFinite α
  have hab : ∃ a b, ¬ π a b := by
    by_contra h
    apply hπ
    apply Setoid.eq_top_iff.mpr
    intro a b
    by_contra hab
    exact h ⟨a, b, hab⟩
  obtain ⟨a, b, hab⟩ := hab
  let G : SimpleGraph α :=
    { Adj := fun x y => ¬ π x y
      symm := ⟨fun x y h hyx => h (π.symm hyx)⟩
      loopless := ⟨fun x h => h (π.refl x)⟩ }
  have travel (x y : α) : Nonempty (G.Walk x y) := by
    by_cases hxy : π x y
    · have hz : ∃ z, ¬ π x z := by
        by_cases hxa : π x a
        · exact ⟨b, fun hxb => hab (π.trans (π.symm hxa) hxb)⟩
        · exact ⟨a, hxa⟩
      obtain ⟨z, hz⟩ := hz
      exact ⟨SimpleGraph.Walk.cons hz
        (SimpleGraph.Walk.cons (fun hzy => hz (π.trans hxy (π.symm hzy))) .nil)⟩
    · exact ⟨SimpleGraph.Walk.cons hxy .nil⟩
  have gather (s : Finset (α × α)) : ∃ p : G.Walk a a,
      ∀ x y, (x, y) ∈ s → ¬ π x y → s(x, y) ∈ p.edges := by
    induction s using Finset.induction_on with
    | empty => exact ⟨.nil, by simp⟩
    | @insert z s hz ih =>
      obtain ⟨p, hp⟩ := ih
      by_cases h : π z.1 z.2
      · refine ⟨p, ?_⟩
        intro x y hxy hn
        rcases Finset.mem_insert.mp hxy with he | he
        · cases he; exact (hn h).elim
        · exact hp x y he hn
      · obtain ⟨p₁⟩ := travel a z.1
        obtain ⟨p₂⟩ := travel z.2 a
        refine ⟨p.append (p₁.append (SimpleGraph.Walk.cons h p₂)), ?_⟩
        intro x y hxy hn
        rcases Finset.mem_insert.mp hxy with he | he
        · cases he
          simp [SimpleGraph.Walk.edges_append]
        · simp only [SimpleGraph.Walk.edges_append, List.mem_append]
          exact Or.inl (hp x y he hn)
  obtain ⟨p, hp⟩ := gather Finset.univ
  have hlen : 0 < p.length := by
    have := List.length_pos_of_mem (hp a b (Finset.mem_univ _) hab)
    simpa using this
  refine ⟨p.length, hlen, fun j => p.getVert j.val, ?_, ?_⟩
  · intro k
    exact p.adj_getVert_succ k.isLt
  · intro x y hxy
    obtain ⟨k, hk, he⟩ := (p.mk_mem_edges_iff_exists).mp (hp x y (Finset.mem_univ _) hxy)
    exact ⟨⟨k, hk⟩, Sym2.eq_iff.mp he⟩

/-- Removing edges whose endpoint colours belong to the same equivalence class. -/
noncomputable def maskedAdjacency {α : Type*} {N : ℕ} (σ : Setoid α)
    (c : Fin N → α) (A : Matrix (Fin N) (Fin N) (ZMod 2)) :
    Matrix (Fin N) (Fin N) (ZMod 2) := by
  classical
  exact fun i j => if σ (c i) (c j) then 0 else A i j

private theorem adjacency_symmetric {n : ℕ} (w : Fin n → Bool) :
    (adjacency w).IsSymm := by
  induction n with
  | zero => simp [adjacency]
  | succ n ih =>
      ext i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j <;> rfl
      · refine Fin.cases ?_ (fun j => ?_) j
        · rfl
        · exact congrFun (congrFun (ih (fun k => w k.succ)) i) j

private theorem adjacency_diag {n : ℕ} (w : Fin n → Bool) (i : Fin (n + 1)) :
    adjacency w i i = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact ih (fun k => w k.succ) j

private theorem masked_path {α : Type*} {n : ℕ} (σ : Setoid α)
    (c : Fin (n + 1) → α) (w : Fin n → Bool) :
    maskedAdjacency σ c (adjacency w) =
      adjacency (fun j => w j && decide (¬ σ (c j.castSucc) (c j.succ))) := by
  classical
  induction n with
  | zero => ext i j; fin_cases i; fin_cases j; simp [maskedAdjacency, adjacency]
  | succ n ih =>
      ext i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [maskedAdjacency, adjacency]
        · refine Fin.cases ?_ (fun k => ?_) j
          · change (if σ (c 0) (c 1) then 0 else if w 0 then 1 else 0) =
              (if w 0 && decide (¬ σ (c 0) (c 1)) then 1 else 0)
            by_cases h : σ (c 0) (c 1) <;> simp [h]
          · simp [maskedAdjacency, adjacency, Fin.succ_ne_zero]
      · refine Fin.cases ?_ (fun j => ?_) j
        · refine Fin.cases ?_ (fun k => ?_) i
          · change (if σ (c 1) (c 0) then 0 else if w 0 then 1 else 0) =
              (if w 0 && decide (¬ σ (c 0) (c 1)) then 1 else 0)
            have hs : σ (c 1) (c 0) ↔ σ (c 0) (c 1) := ⟨σ.symm, σ.symm⟩
            by_cases h : σ (c 0) (c 1) <;> simp [hs, h]
          · simp [maskedAdjacency, adjacency, Fin.succ_ne_zero]
        · exact congrFun (congrFun (ih (Fin.tail c) (Fin.tail w)) i) j

/-- A single coloured path separates a partition from every partition not refining it.
The same path and colour word are used for all test partitions. -/
theorem path_separator {α : Type*} [Finite α] (π : Setoid α) (hπ : π ≠ ⊤) :
    ∃ (n : ℕ) (_ : 0 < n) (c : Fin (n + 1) → α), ∀ σ : Setoid α,
      (∑ w : Fin n → Bool,
        (-1 : ℤ) ^ (Finset.univ.filter (fun j => w j = true)).card *
          (maskedAdjacency σ c (adjacency w)).rank) = if σ ≤ π then -2 else 0 := by
  classical
  obtain ⟨n, hn, c, hc, hcover⟩ := exists_color_word π hπ
  refine ⟨n, hn, c, fun σ => ?_⟩
  simp only [masked_path, ← edgeSign_eq]
  rw [masked_alternating_rank hn]
  congr 1
  simp only [decide_eq_true_eq]
  apply propext
  constructor
  · intro h x y hσ
    by_contra hπxy
    obtain ⟨k, hk | hk⟩ := hcover x y hπxy
    · exact h k (hk.1.symm ▸ hk.2.symm ▸ hσ)
    · exact h k (hk.1.symm ▸ hk.2.symm ▸ σ.symm hσ)
  · intro h k hσ
    exact hc k (h hσ)

private theorem independent_setoids {α ι : Type*} [Finite α] [Fintype ι]
    (p : ι → Setoid α) (hp : Function.Injective p) (hproper : ∀ i, p i ≠ ⊤)
    (a : ι → ℝ)
    (h : ∀ (N : ℕ) (A : Matrix (Fin N) (Fin N) (ZMod 2)),
      A.IsSymm → (∀ j, A j j = 0) → ∀ c : Fin N → α,
        ∑ i, a i * ((maskedAdjacency (p i) c A).rank : ℝ) = 0) : ∀ i, a i = 0 := by
  classical
  have zeta (i : ι) : ∑ j with p j ≤ p i, a j = 0 := by
    obtain ⟨n, hn, c, hc⟩ := path_separator (p i) (hproper i)
    have he (j : ι) : (∑ w : Fin n → Bool,
        ((-1 : ℤ) ^ (Finset.univ.filter (fun k => w k = true)).card : ℝ) *
          ((maskedAdjacency (p j) c (adjacency w)).rank : ℝ)) =
        if p j ≤ p i then -2 else 0 := by
      exact_mod_cast hc (p j)
    have hh : (∑ w : Fin n → Bool,
        ((-1 : ℤ) ^ (Finset.univ.filter (fun k => w k = true)).card : ℝ) *
          ∑ j, a j * ((maskedAdjacency (p j) c (adjacency w)).rank : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro w _
      rw [h (n + 1) (adjacency w) (adjacency_symmetric w) (adjacency_diag w) c, mul_zero]
    simp_rw [Finset.mul_sum] at hh
    rw [Finset.sum_comm] at hh
    have hswap (j : ι) : (∑ w : Fin n → Bool,
        ((-1 : ℤ) ^ (Finset.univ.filter (fun k => w k = true)).card : ℝ) *
          (a j * ((maskedAdjacency (p j) c (adjacency w)).rank : ℝ))) =
        a j * (if p j ≤ p i then -2 else 0) := by
      rw [← he j, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    simp_rw [hswap, mul_ite, mul_zero] at hh
    rw [← Finset.sum_filter, ← Finset.sum_mul] at hh
    exact (mul_eq_zero.mp hh).resolve_right (by norm_num)
  by_contra hn
  push Not at hn
  obtain ⟨i, hi⟩ := hn
  obtain ⟨j, hj, hmin⟩ := Finset.exists_minimalFor p
    (Finset.univ.filter (fun k => a k ≠ 0)) ⟨i, by simp [hi]⟩
  have hjne : a j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hjzero : (∑ k with p k ≤ p j, a k) = a j := by
    apply Finset.sum_eq_single j
    · intro k hk hkj
      by_contra hkne
      have hle := hmin (by simp [hkne]) (Finset.mem_filter.mp hk).2
      exact hkj (hp (le_antisymm (Finset.mem_filter.mp hk).2 hle))
    · simp
  exact hjne (hjzero.symm.trans (zeta j))

private theorem partition_kernel_injective {α : Type*} [Fintype α] [DecidableEq α] :
    Function.Injective (fun P : Finpartition (Finset.univ : Finset α) => Setoid.ker P.part) := by
  intro P Q h
  have he (x y : α) : P.part x = P.part y ↔ Q.part x = Q.part y := by
    exact Iff.of_eq (congrArg (fun s : Setoid α => s x y) h)
  have hpart (x : α) : P.part x = Q.part x := by
    ext y
    simpa only [P.mem_part_iff_part_eq_part (Finset.mem_univ _) (Finset.mem_univ _),
      Q.mem_part_iff_part_eq_part (Finset.mem_univ _) (Finset.mem_univ _)] using he y x
  apply Finpartition.ext
  ext t
  constructor
  · intro ht
    obtain ⟨x, hx, heq⟩ := P.part_surjOn ht
    rw [← heq, hpart]
    exact Q.part_mem.mpr hx
  · intro ht
    obtain ⟨x, hx, heq⟩ := Q.part_surjOn ht
    rw [← heq, ← hpart]
    exact P.part_mem.mpr hx

private theorem partition_kernel_ne_top {α : Type*} [Fintype α] [DecidableEq α]
    (P : Finpartition (Finset.univ : Finset α)) (hP : 2 ≤ P.parts.card) :
    Setoid.ker P.part ≠ ⊤ := by
  intro h
  have hc : P.parts.card ≤ 1 := Finset.card_le_one.mpr (by
    intro s hs t ht
    obtain ⟨x, _, hx⟩ := P.part_surjOn hs
    obtain ⟨y, _, hy⟩ := P.part_surjOn ht
    have he := Setoid.eq_top_iff.mp h x y
    change P.part x = P.part y at he
    simpa [hx, hy] using he)
  omega

set_option maxHeartbeats 600000 in
-- Elaborating the finite partition subtype requires its nested finite-set instances.
/-- The two- and three-block partition rank functions are linearly independent.
Every number of vertices, symmetric zero-diagonal binary matrix, and colouring is quantified. -/
theorem partition_rank_independent (q : ℕ) (_hq : 2 ≤ q)
    (a : {P : Finpartition (Finset.univ : Finset (Fin q)) //
      P.parts.card = 2 ∨ P.parts.card = 3} → ℝ)
    (h : ∀ (N : ℕ) (A : Matrix (Fin N) (Fin N) (ZMod 2)),
      A.IsSymm → (∀ j, A j j = 0) → ∀ c : Fin N → Fin q,
        ∑ P, a P * ((maskedAdjacency (Setoid.ker P.val.part) c A).rank : ℝ) = 0) :
    ∀ P, a P = 0 := by
  refine independent_setoids
    (fun P : {P : Finpartition (Finset.univ : Finset (Fin q)) //
      P.parts.card = 2 ∨ P.parts.card = 3} => Setoid.ker P.val.part) ?_ ?_ a h
  · intro P Q he
    exact Subtype.ext (partition_kernel_injective he)
  · intro P
    apply partition_kernel_ne_top
    rcases P.property with hp | hp <;> omega


end D5.S3.Combinatorics.Graph.Paths.AlternatingRank
