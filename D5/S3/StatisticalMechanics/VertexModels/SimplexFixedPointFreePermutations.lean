/- GID: D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: A fixed-point-free permutation solves the n-simplex equation iff n is even. -/

/-
proof_shape: result: content; private chain_values: content
escape_witness: chain_values computes, by following each edge through the vertex operators in
  increasing and in decreasing order, the two sides of the equation at the edge {i, i + 1} for
  every map and at every edge for every map moving each index by at most one; result turns
  these into |s(i) - i| ≤ 1, a parity count for fixed-point-free permutations, and a
  solution for the product of adjacent transpositions.
admission_basis: open-problem-resolution (#11874; Proved)
Direct frozen dependencies: none (Mathlib only).
Utility: none; the result is a theorem over every n.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Finset

namespace D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations

/-- The edges `{a, b}`, `a < b ≤ n`, of the complete graph on the vertices `0, …, n` of the
`n`-simplex. They index the `n (n + 1) / 2` coordinates of the `n`-simplex equation: the paper's
matrix `MI_n` numbers them so that its row `v` lists the edges at `v`. -/
abbrev Edge (n : ℕ) : Type := {p : ℕ × ℕ // p.1 < p.2 ∧ p.2 ≤ n}

/-- The edge in slot `j` at the vertex `v`: the edge from `v` to the `j`-th of the other `n`
vertices in increasing order, which is `j` when `j < v` and `j + 1` otherwise. -/
def slotEdge {n : ℕ} (v : Fin (n + 1)) (j : Fin n) : Edge n :=
  if h : j.val < v.val then ⟨(j.val, v.val), h, by have := v.isLt; omega⟩
  else ⟨(v.val, j.val + 1), by omega, by have := j.isLt; omega⟩

/-- The operator `R_v`: it applies `T` to the coordinates on the `n` edges at the vertex `v`,
taken in slot order, and leaves the other coordinates unchanged. -/
def opR {X : Type*} {n : ℕ} (T : (Fin n → X) → Fin n → X) (v : Fin (n + 1))
    (x : Edge n → X) (e : Edge n) : X :=
  if e.1.1 = v.val then T (fun j => x (slotEdge v j)) ⟨e.1.2 - 1, by have := e.2; omega⟩
  else if e.1.2 = v.val then T (fun j => x (slotEdge v j)) ⟨e.1.1, by have := e.2; omega⟩
  else x e

/-- The product `R_0 R_1 ⋯ R_(k-1)` of the first `k` vertex operators, as a composition of maps
of `X^N`. -/
def lhs {X : Type*} {n : ℕ} (T : (Fin n → X) → Fin n → X) : ℕ → (Edge n → X) → Edge n → X
  | 0 => id
  | k + 1 => if h : k < n + 1 then lhs T k ∘ opR T ⟨k, h⟩ else lhs T k

/-- The product `R_(k-1) ⋯ R_1 R_0` of the first `k` vertex operators in reverse order. -/
def rhs {X : Type*} {n : ℕ} (T : (Fin n → X) → Fin n → X) : ℕ → (Edge n → X) → Edge n → X
  | 0 => id
  | k + 1 => if h : k < n + 1 then opR T ⟨k, h⟩ ∘ rhs T k else rhs T k

/-- The `n`-simplex equation `R_0 R_1 ⋯ R_n = R_n ⋯ R_1 R_0` for the map `T : X^n → X^n`. -/
def IsSolution {X : Type*} (n : ℕ) (T : (Fin n → X) → Fin n → X) : Prop :=
  lhs T (n + 1) = rhs T (n + 1)

/-- The simple map `T_s(x_1, …, x_n) = (x_{s(1)}, …, x_{s(n)})`. -/
def simpleMap {X : Type*} {n : ℕ} (s : Fin n → Fin n) (y : Fin n → X) : Fin n → X :=
  fun j => y (s j)

/-- Question 2 of Bardakov et al. (arXiv:2206.08906, Question 4.22 of the journal version),
answered: for `n > 2` there is a permutation without fixed points whose simple map solves the
`n`-simplex equation on every set exactly when `n` is even. `result` proves it. -/
def claim : Prop :=
  ∀ n : ℕ, 2 < n →
    ((∃ s : Equiv.Perm (Fin n), (∀ i, s i ≠ i) ∧
      ∀ X : Type, IsSolution n (simpleMap (X := X) s)) ↔ Even n)

/-- The edge from `v` to the vertex in slot `j`, as a pair of naturals. -/
private def mkE (v j : ℕ) : ℕ × ℕ := if j < v then (j, v) else (v, j + 1)

/-- The action on edges of the operator of the vertex `v` for the simple map of `f`. -/
private def sigN (f : ℕ → ℕ) (v : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.1 = v then mkE v (f (p.2 - 1)) else if p.2 = v then mkE v (f p.1) else p

/-- The edges reached through the vertices `0, 1, …, k - 1` in increasing order. -/
private def upN (f : ℕ → ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, p => p
  | k + 1, p => sigN f k (upN f k p)

/-- The edges reached through the vertices `k - 1, …, 1, 0` in decreasing order. -/
private def downN (f : ℕ → ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, p => p
  | k + 1, p => downN f k (sigN f k p)

/-- The two sides of the equation at the edges: at `{i, i + 1}` for every map, and at every edge
for every map that moves each index by at most one. -/
private theorem chain_values (f : ℕ → ℕ) (n : ℕ) :
    (∀ i, i < n → f i < n →
      upN f (n + 1) (i, i + 1) = (if i ≤ f i then (f i, f i + 1) else (f i, i)) ∧
      downN f (n + 1) (i, i + 1) = (if f i ≤ i then (f i, f i + 1) else (i + 1, f i + 1))) ∧
    ((∀ j, j < n → f j < n ∧ f j ≤ j + 1 ∧ j ≤ f j + 1) →
      ∀ a b, a < b → b ≤ n → upN f (n + 1) (a, b) = downN f (n + 1) (a, b)) := by
  have fix : ∀ v p, p.1 ≠ v → p.2 ≠ v → sigN f v p = p := by
    intro v p h1 h2
    simp [sigN, h1, h2]
  have frameUp : ∀ j m p, (∀ v, j ≤ v → v < j + m → (upN f j p).1 ≠ v ∧ (upN f j p).2 ≠ v) →
      upN f (j + m) p = upN f j p := by
    intro j m p h
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [show j + (m + 1) = (j + m) + 1 by ring, upN,
        ih (fun v h1 h2 => h v h1 (by omega))]
      exact fix _ _ (h (j + m) (by omega) (by omega)).1 (h (j + m) (by omega) (by omega)).2
  have frameDown : ∀ j m p, (∀ v, j ≤ v → v < j + m → p.1 ≠ v ∧ p.2 ≠ v) →
      downN f (j + m) p = downN f j p := by
    intro j m p h
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [show j + (m + 1) = (j + m) + 1 by ring, downN,
        fix _ _ (h (j + m) (by omega) (by omega)).1 (h (j + m) (by omega) (by omega)).2,
        ih (fun v h1 h2 => h v h1 (by omega))]
  -- `upN` from `j` to `k` and `downN` from `k` to `j` over vertices away from the edge
  have upTo : ∀ j k p, j ≤ k → (∀ v, j ≤ v → v < k → (upN f j p).1 ≠ v ∧ (upN f j p).2 ≠ v) →
      upN f k p = upN f j p := by
    intro j k p hjk h
    obtain ⟨m, rfl⟩ : ∃ m, k = j + m := ⟨k - j, by omega⟩
    exact frameUp j m p h
  have downTo : ∀ j k p, j ≤ k → (∀ v, j ≤ v → v < k → p.1 ≠ v ∧ p.2 ≠ v) →
      downN f k p = downN f j p := by
    intro j k p hjk h
    obtain ⟨m, rfl⟩ : ∃ m, k = j + m := ⟨k - j, by omega⟩
    exact frameDown j m p h
  have upZero : ∀ p, upN f 0 p = p := fun _ => rfl
  have downZero : ∀ p, downN f 0 p = p := fun _ => rfl
  have mkLt : ∀ v j, j < v → mkE v j = (j, v) := fun v j h => if_pos h
  have mkGe : ∀ v j, v ≤ j → mkE v j = (v, j + 1) := fun v j h => if_neg (by omega)
  have sigLeft : ∀ v b, v < b → sigN f v (v, b) = mkE v (f (b - 1)) := by
    intro v b _
    simp [sigN]
  have sigRight : ∀ a v, a < v → sigN f v (a, v) = mkE v (f a) := by
    intro a v h
    simp [sigN, show a ≠ v by omega]
  refine ⟨fun i hi hfi => ⟨?_, ?_⟩, fun hnear a b hab hb => ?_⟩
  · -- increasing order at the edge `{i, i + 1}`
    have h0 : upN f i (i, i + 1) = (i, i + 1) := by
      rw [upTo 0 i (i, i + 1) (by omega) (fun v _ hv => by simp only [upZero]; omega), upZero]
    have h1 : upN f (i + 1) (i, i + 1) = mkE i (f i) := by
      rw [upN, h0, sigLeft i (i + 1) (by omega)]
      simp
    by_cases hc : i ≤ f i
    · rw [if_pos hc]
      rw [mkGe i (f i) hc] at h1
      have h2 : upN f (f i + 1) (i, i + 1) = (i, f i + 1) := by
        rw [upTo (i + 1) (f i + 1) (i, i + 1) (by omega)
          (fun v h1' h2' => by rw [h1]; omega), h1]
      have h3 : upN f (f i + 2) (i, i + 1) = (f i, f i + 1) := by
        rw [upN, h2, sigRight i (f i + 1) (by omega), mkLt (f i + 1) (f i) (by omega)]
      rw [upTo (f i + 2) (n + 1) (i, i + 1) (by omega) (fun v h1' h2' => by rw [h3]; omega), h3]
    · rw [if_neg hc]
      rw [mkLt i (f i) (by omega)] at h1
      rw [upTo (i + 1) (n + 1) (i, i + 1) (by omega) (fun v h1' h2' => by rw [h1]; omega), h1]
  · -- decreasing order at the edge `{i, i + 1}`
    have h0 : downN f (n + 1) (i, i + 1) = downN f (i + 2) (i, i + 1) :=
      downTo (i + 2) (n + 1) (i, i + 1) (by omega) (fun v h1' h2' => by omega)
    have h1 : downN f (i + 2) (i, i + 1) = downN f (i + 1) (mkE (i + 1) (f i)) := by
      rw [downN, sigRight i (i + 1) (by omega)]
    rw [h0, h1]
    by_cases hc : f i ≤ i
    · rw [if_pos hc, mkLt (i + 1) (f i) (by omega)]
      rw [downTo (f i + 1) (i + 1) (f i, i + 1) (by omega) (fun v h1' h2' => by omega), downN,
        sigLeft (f i) (i + 1) (by omega), show i + 1 - 1 = i by omega,
        mkGe (f i) (f i) le_rfl,
        downTo 0 (f i) (f i, f i + 1) (by omega) (fun v h1' h2' => by omega), downZero]
    · rw [if_neg hc, mkGe (i + 1) (f i) (by omega),
        downTo 0 (i + 1) (i + 1, f i + 1) (by omega) (fun v h1' h2' => by omega), downZero]
  · -- every edge, for a map moving each index by at most one
    have ha := hnear a (by omega)
    have hb1 := hnear (b - 1) (by omega)
    have u0 : upN f a (a, b) = (a, b) := by
      rw [upTo 0 a (a, b) (by omega) (fun v _ hv => by simp only [upZero]; omega), upZero]
    have u1 : upN f (a + 1) (a, b) = mkE a (f (b - 1)) := by
      rw [upN, u0, sigLeft a b hab]
    have d0 : downN f (n + 1) (a, b) = downN f b (mkE b (f a)) := by
      rw [downTo (b + 1) (n + 1) (a, b) (by omega) (fun v h1' h2' => by omega), downN,
        sigRight a b hab]
    rcases Nat.lt_or_ge b (a + 2) with hb2 | hb2
    · -- the edge `{a, a + 1}`
      obtain rfl : b = a + 1 := by omega
      rw [show a + 1 - 1 = a by omega] at u1
      have down : downN f (n + 1) (a, a + 1) = (f a, f a + 1) := by
        rw [d0]
        by_cases h : f a < a + 1
        · rw [mkLt (a + 1) (f a) h,
            downTo (f a + 1) (a + 1) (f a, a + 1) (by omega) (fun v h1' h2' => by omega),
            downN, sigLeft (f a) (a + 1) (by omega), show a + 1 - 1 = a by omega,
            mkGe (f a) (f a) le_rfl,
            downTo 0 (f a) (f a, f a + 1) (by omega) (fun v h1' h2' => by omega), downZero]
        · rw [mkGe (a + 1) (f a) (by omega),
            downTo 0 (a + 1) (a + 1, f a + 1) (by omega) (fun v h1' h2' => by omega),
            downZero]
          rw [Prod.mk.injEq]
          omega
      rw [down]
      by_cases h : f a < a
      · rw [mkLt a (f a) h] at u1
        rw [upTo (a + 1) (n + 1) (a, a + 1) (by omega) (fun v h1' h2' => by rw [u1]; omega),
          u1]
        rw [Prod.mk.injEq]
        omega
      · rw [mkGe a (f a) (by omega)] at u1
        have u2 : upN f (f a + 1) (a, a + 1) = (a, f a + 1) := by
          rw [upTo (a + 1) (f a + 1) (a, a + 1) (by omega)
            (fun v h1' h2' => by rw [u1]; omega), u1]
        have u3 : upN f (f a + 2) (a, a + 1) = (f a, f a + 1) := by
          rw [upN, u2, sigRight a (f a + 1) (by omega), mkLt (f a + 1) (f a) (by omega)]
        rw [upTo (f a + 2) (n + 1) (a, a + 1) (by omega)
          (fun v h1' h2' => by rw [u3]; omega), u3]
    · -- the edges `{a, b}` with `b ≥ a + 2`
      rw [mkGe a (f (b - 1)) (by omega)] at u1
      have u2 : upN f (f (b - 1) + 1) (a, b) = (a, f (b - 1) + 1) := by
        rw [upTo (a + 1) (f (b - 1) + 1) (a, b) (by omega)
          (fun v h1' h2' => by rw [u1]; omega), u1]
      have u3 : upN f (f (b - 1) + 2) (a, b) = mkE (f (b - 1) + 1) (f a) := by
        rw [upN, u2, sigRight a (f (b - 1) + 1) (by omega)]
      rw [d0, mkLt b (f a) (by omega),
        downTo (f a + 1) b (f a, b) (by omega) (fun v h1' h2' => by omega), downN,
        sigLeft (f a) b (by omega)]
      by_cases hu : f a ≤ f (b - 1)
      · rw [mkLt (f (b - 1) + 1) (f a) (by omega)] at u3
        rw [upTo (f (b - 1) + 2) (n + 1) (a, b) (by omega)
          (fun v h1' h2' => by rw [u3]; omega), u3, mkGe (f a) (f (b - 1)) hu,
          downTo 0 (f a) (f a, f (b - 1) + 1) (by omega) (fun v h1' h2' => by omega),
          downZero]
      · -- then `b = a + 2`, `f a = a + 1` and `f (a + 1) = a`
        have hfa : f a = a + 1 := by omega
        have hft : f (b - 1) = a := by omega
        obtain rfl : b = a + 2 := by omega
        rw [show a + 2 - 1 = a + 1 by omega] at hft u3 ⊢
        rw [hft, hfa, mkGe (a + 1) (a + 1) le_rfl] at u3
        have u4 : upN f (a + 3) (a, a + 2) = (a, a + 2) := by
          rw [upN, u3, sigRight (a + 1) (a + 2) (by omega), hft, mkLt (a + 2) a (by omega)]
        rw [upTo (a + 3) (n + 1) (a, a + 2) (by omega) (fun v h1' h2' => by rw [u4]; omega),
          u4, hft, hfa, mkLt (a + 1) a (by omega), downN, sigLeft a (a + 1) (by omega),
          show a + 1 - 1 = a by omega, hfa, mkGe a (a + 1) (by omega),
          downTo 0 a (a, a + 1 + 1) (by omega) (fun v h1' h2' => by omega), downZero]

theorem result : claim := by
  intro n hn
  -- the operator of a vertex moves the coordinate of one edge to another edge
  have stepEdge : ∀ (s : Fin n → Fin n) (v : Fin (n + 1)) (e : Edge n), ∃ e' : Edge n,
      e'.1 = sigN (fun j => if h : j < n then (s ⟨j, h⟩).val else 0) v.val e.1 ∧
      ∀ (X : Type) (x : Edge n → X), opR (simpleMap s) v x e = x e' := by
    intro s v e
    have hslot : ∀ j : Fin n, (slotEdge v j).1 = mkE v.val j.val := by
      intro j
      unfold slotEdge mkE
      by_cases h : j.val < v.val
      · rw [dif_pos h, if_pos h]
      · rw [dif_neg h, if_neg h]
    by_cases h1 : e.1.1 = v.val
    · refine ⟨slotEdge v (s ⟨e.1.2 - 1, by have := e.2; omega⟩), ?_, fun X x => ?_⟩
      · rw [hslot]
        unfold sigN
        rw [if_pos h1]
        beta_reduce
        rw [dif_pos (by have := e.2; omega)]
      · unfold opR simpleMap
        rw [if_pos h1]
    · by_cases h2 : e.1.2 = v.val
      · refine ⟨slotEdge v (s ⟨e.1.1, by have := e.2; omega⟩), ?_, fun X x => ?_⟩
        · rw [hslot]
          unfold sigN
          rw [if_neg h1, if_pos h2]
          beta_reduce
          rw [dif_pos (by have := e.2; omega)]
        · unfold opR simpleMap
          rw [if_neg h1, if_pos h2]
      · refine ⟨e, ?_, fun X x => ?_⟩
        · unfold sigN
          rw [if_neg h1, if_neg h2]
        · unfold opR
          rw [if_neg h1, if_neg h2]
  -- the two sides of the equation for a simple map, edge by edge
  have bridgeL : ∀ (s : Fin n → Fin n) (k : ℕ) (e : Edge n), ∃ e' : Edge n,
      e'.1 = upN (fun j => if h : j < n then (s ⟨j, h⟩).val else 0) k e.1 ∧
      ∀ (X : Type) (x : Edge n → X), lhs (simpleMap s) k x e = x e' := by
    intro s k e
    induction k with
    | zero => exact ⟨e, rfl, fun X x => rfl⟩
    | succ k ih =>
      obtain ⟨ek, hek, hx⟩ := ih
      by_cases hk : k < n + 1
      · obtain ⟨e', he', hx'⟩ := stepEdge s ⟨k, hk⟩ ek
        refine ⟨e', ?_, fun X x => ?_⟩
        · rw [he', hek]
          rfl
        · rw [lhs, dif_pos hk, Function.comp_apply, hx, hx']
      · refine ⟨ek, ?_, fun X x => ?_⟩
        · have := ek.2
          change ek.1 = sigN _ k (upN _ k e.1)
          rw [← hek]
          unfold sigN
          rw [if_neg (by omega), if_neg (by omega)]
        · rw [lhs, dif_neg hk, hx]
  have bridgeR : ∀ (s : Fin n → Fin n) (k : ℕ) (e : Edge n), ∃ e' : Edge n,
      e'.1 = downN (fun j => if h : j < n then (s ⟨j, h⟩).val else 0) k e.1 ∧
      ∀ (X : Type) (x : Edge n → X), rhs (simpleMap s) k x e = x e' := by
    intro s k
    induction k with
    | zero => exact fun e => ⟨e, rfl, fun X x => rfl⟩
    | succ k ih =>
      intro e
      by_cases hk : k < n + 1
      · obtain ⟨e1, he1, hx1⟩ := stepEdge s ⟨k, hk⟩ e
        obtain ⟨e', he', hx'⟩ := ih e1
        refine ⟨e', ?_, fun X x => ?_⟩
        · rw [he', he1]
          rfl
        · rw [rhs, dif_pos hk, Function.comp_apply, hx1, hx']
      · obtain ⟨e', he', hx'⟩ := ih e
        refine ⟨e', ?_, fun X x => ?_⟩
        · have := e.2
          rw [he']
          change _ = downN _ k (sigN _ k e.1)
          unfold sigN
          rw [if_neg (by omega), if_neg (by omega)]
        · rw [rhs, dif_neg hk, hx']
  -- a simple map solves the equation on every set iff the two edge maps agree
  have simpleSol : ∀ s : Fin n → Fin n,
      (∀ e : Edge n, upN (fun j => if h : j < n then (s ⟨j, h⟩).val else 0) (n + 1) e.1 =
        downN (fun j => if h : j < n then (s ⟨j, h⟩).val else 0) (n + 1) e.1) ↔
      ∀ X : Type, IsSolution n (simpleMap (X := X) s) := by
    intro s
    constructor
    · intro h X
      funext x e
      obtain ⟨e1, he1, hx1⟩ := bridgeL s (n + 1) e
      obtain ⟨e2, he2, hx2⟩ := bridgeR s (n + 1) e
      rw [hx1, hx2, Subtype.ext (he1.trans ((h e).trans he2.symm))]
    · intro h e
      obtain ⟨e1, he1, hx1⟩ := bridgeL s (n + 1) e
      obtain ⟨e2, he2, hx2⟩ := bridgeR s (n + 1) e
      have := congrFun (congrFun (h (Edge n)) id) e
      rw [hx1, hx2] at this
      rw [← he1, ← he2]
      exact congrArg Subtype.val this
  constructor
  · rintro ⟨s, hfix, hsol⟩
    have heq := (simpleSol s).2 hsol
    set f : ℕ → ℕ := fun j => if h : j < n then (s ⟨j, h⟩).val else 0 with hf
    -- every index moves by exactly one
    have near : ∀ i : Fin n, (s i).val = i.val + 1 ∨ (s i).val + 1 = i.val := by
      intro i
      have hfi : f i.val = (s i).val := by simp [hf, i.isLt]
      obtain ⟨hu, hd⟩ := (chain_values f n).1 i.val i.isLt (by rw [hfi]; exact (s i).isLt)
      have h : upN f (n + 1) (i.val, i.val + 1) = downN f (n + 1) (i.val, i.val + 1) :=
        heq ⟨(i.val, i.val + 1), by omega, by have := i.isLt; omega⟩
      rw [hu, hd, hfi] at h
      have hne : (s i).val ≠ i.val := fun h' => hfix i (Fin.ext h')
      split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> omega
    -- the displacements `s i - i` are `±1` and sum to `0`
    have hsum : ∑ i : Fin n, ((s i).val : ℤ) = ∑ i : Fin n, (i.val : ℤ) :=
      Equiv.sum_comp s (fun i => (i.val : ℤ))
    have heven : Even (∑ i : Fin n, (((s i).val : ℤ) - i.val + 1)) := by
      apply even_sum
      intro i _
      rcases near i with h | h
      · exact ⟨1, by rw [show ((s i).val : ℤ) = i.val + 1 by exact_mod_cast h]; ring⟩
      · exact ⟨0, by
          rw [show ((s i).val : ℤ) = i.val - 1 by
            have : ((s i).val : ℤ) + 1 = i.val := by exact_mod_cast h
            linarith]
          ring⟩
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum, sub_self, zero_add] at heven
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at heven
    exact_mod_cast heven
  · rintro ⟨m, hm⟩
    -- the product of the transpositions of `2t` and `2t + 1`
    let g : Fin n → Fin n := fun j =>
      ⟨if j.val % 2 = 0 then j.val + 1 else j.val - 1, by have := j.isLt; split_ifs <;> omega⟩
    have hg : Function.Involutive g := by
      intro j
      apply Fin.ext
      simp only [g]
      split_ifs <;> omega
    refine ⟨hg.toPerm g, fun i h => ?_, fun X => ?_⟩
    · have h' := congrArg Fin.val h
      simp only [Function.Involutive.coe_toPerm, g] at h'
      split_ifs at h' <;> omega
    · refine (simpleSol (hg.toPerm g)).1 (fun e => ?_) X
      obtain ⟨⟨a, b⟩, hab, hb⟩ := e
      refine (chain_values _ n).2 (fun j hj => ?_) a b hab hb
      simp only [Function.Involutive.coe_toPerm, g, dif_pos hj]
      split_ifs <;> omega

end D5.S3.StatisticalMechanics.VertexModels.SimplexFixedPointFreePermutations
