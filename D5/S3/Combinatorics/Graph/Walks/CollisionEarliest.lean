/- GID: D5/S3/Combinatorics/Graph/Walks/CollisionEarliest
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/CollisionEarliest
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: The earliest full-coverage edge collision is counted by n!: T(n, n + 1) = n!. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#232)
escape_witness: walkEquiv (collision walks of length n + 1 from v correspond to orderings of
  the vertices starting at v together with a revisit vertex: the first n positions form a
  bijection, position n is free, and the last vertex is forced by build_pre).
proof_shape:
  pre, build: private definitions; consumers: the lemmas below.
  edge_initial, edge_last, build_lt, build_N: bind-only helpers (definitional unfolding);
    consumers: repeat_index, build_succ, build_collision, build_agree, walkEquiv.
  repeat_index: bind-only helper (projection of Collision); consumers: pre_surjective,
    build_pre.
  pre_surjective: content; consumer: pre_bijective.
  pre_bijective: bind-only helper (finite injective iff surjective); consumers: build_agree,
    build_pre, walkEquiv.
  build_succ, build_agree: bind-only helpers (unfolding and case split); consumers:
    build_collision, build_pre.
  build_collision, build_pre: content; consumer: walkEquiv.
  walkEquiv: content; consumer: earliest_count.
  startEquiv: bind-only helper (fiber of Equiv.Perm.decomposeFin over v); consumer:
    earliest_count.
  earliest_count: content.
Direct frozen dependencies: D5/S3/Combinatorics/Graph/Walks/CollisionPrefix (Walk, edge,
  initialWalk, Collision, OrderedEdges, SourceCollision, sourceCollisionEquiv,
  collisionCount; statement_id
  sha256:f52bf4d7accfeb8c63303a05d8417fcc99fba893d4c84829e5334937f2ee43ae).
Search record (§3.1): CollisionPrefix proves the late-collision identities, ratio and
  positivity but no count at k = n + 1; no D5 declaration counts walks against n!. Mathlib
  supplies Equiv.Perm.decomposeFin and Fintype.card_perm.
-/

import D5.S3.Combinatorics.Graph.Walks.CollisionPrefix
import Mathlib.GroupTheory.Perm.Fin

/-! # The earliest full-coverage edge collision

A walk counted by `T(n, n + 1)` has `n + 2` vertices. Its last edge repeats an earlier one,
so its first `n + 1` vertices, and in fact its first `n` vertices, already visit every vertex.
Hence the first `n` vertices are an ordering of the vertices starting at `v`, the vertex at
position `n` is arbitrary, and the last vertex is the successor of the first visit to it.
This gives `(n - 1)! · n = n!` walks.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.CollisionEarliest

open D5.S3.Combinatorics.Graph.Walks.CollisionPrefix

private theorem edge_initial {N : ℕ} (w : Walk (Fin N) (N + 1)) (j : Fin N) :
    edge (initialWalk w) j = (w ⟨j, by omega⟩, w ⟨j + 1, by omega⟩) := rfl

private theorem edge_last {N : ℕ} (w : Walk (Fin N) (N + 1)) :
    edge w (Fin.last N) = (w ⟨N, by omega⟩, w ⟨N + 1, by omega⟩) := rfl

/-- The last edge repeats the edge at some `i < N`. -/
private theorem repeat_index {N : ℕ} {v : Fin N} {w : Walk (Fin N) (N + 1)}
    (h : Collision v w) : ∃ i : Fin N, w ⟨N, by omega⟩ = w ⟨i, by omega⟩ ∧
      w ⟨N + 1, by omega⟩ = w ⟨i + 1, by omega⟩ := by
  obtain ⟨j, hj⟩ := h.2.2.1
  rw [edge_initial, edge_last, Prod.mk.injEq] at hj
  exact ⟨j, hj.1.symm, hj.2.symm⟩

/-- The first `N` vertices of a walk. -/
private def pre {N : ℕ} (w : Walk (Fin N) (N + 1)) (i : Fin N) : Fin N := w ⟨i, by omega⟩

private theorem pre_surjective {N : ℕ} {v : Fin N} {w : Walk (Fin N) (N + 1)}
    (h : Collision v w) : Function.Surjective (pre w) := by
  obtain ⟨i, hN, hN1⟩ := repeat_index h
  intro a
  obtain ⟨t, ht⟩ := h.2.2.2 a
  by_cases h1 : t.val < N
  · exact ⟨⟨t, h1⟩, by simp only [pre]; rw [← ht]⟩
  · by_cases h2 : t.val = N
    · refine ⟨i, ?_⟩
      simp only [pre]
      rw [← hN, ← ht]; congr 1; ext; simp [h2]
    · have h3 : t.val = N + 1 := by omega
      by_cases h4 : i.val + 1 < N
      · refine ⟨⟨i + 1, h4⟩, ?_⟩
        simp only [pre]
        rw [← hN1, ← ht]; congr 1; ext; simp [h3]
      · refine ⟨i, ?_⟩
        simp only [pre]
        have h5 : i.val + 1 = N := by omega
        rw [← hN, ← ht]
        have : (⟨N, by omega⟩ : Fin (N + 2)) = ⟨i + 1, by omega⟩ := by ext; simp [h5]
        rw [this, ← hN1]; congr 1; ext; simp [h3]

private theorem pre_bijective {N : ℕ} {v : Fin N} {w : Walk (Fin N) (N + 1)}
    (h : Collision v w) : Function.Bijective (pre w) :=
  ⟨Finite.injective_iff_surjective.mpr (pre_surjective h), pre_surjective h⟩

/-- The walk determined by an ordering `σ` of the vertices and a revisit vertex `a`. -/
private def build {N : ℕ} (σ : Equiv.Perm (Fin N)) (a : Fin N) : Walk (Fin N) (N + 1) :=
  fun t => if h : t.val < N then σ ⟨t, h⟩ else if t.val = N then a else
    if h2 : (σ.symm a).val + 1 < N then σ ⟨(σ.symm a).val + 1, h2⟩ else a

private theorem build_lt {N : ℕ} (σ : Equiv.Perm (Fin N)) (a : Fin N) (i : ℕ) (hi : i < N) :
    build σ a ⟨i, by omega⟩ = σ ⟨i, hi⟩ := by
  simp [build, hi]

private theorem build_N {N : ℕ} (σ : Equiv.Perm (Fin N)) (a : Fin N) :
    build σ a ⟨N, by omega⟩ = a := by
  simp [build]

private theorem build_succ {N : ℕ} (σ : Equiv.Perm (Fin N)) (a : Fin N) :
    build σ a ⟨N + 1, by omega⟩ = build σ a ⟨(σ.symm a).val + 1, by omega⟩ := by
  have hlt := (σ.symm a).isLt
  by_cases h2 : (σ.symm a).val + 1 < N
  · simp [build, h2]
  · have h3 : (σ.symm a).val + 1 = N := by omega
    simp [build, h3]

private theorem build_collision {N : ℕ} (σ : Equiv.Perm (Fin N)) (a : Fin N) (hN : 0 < N) :
    Collision (σ ⟨0, hN⟩) (build σ a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact build_lt σ a 0 hN
  · intro j k hjk
    rw [edge_initial, edge_initial, Prod.mk.injEq, build_lt σ a j j.isLt,
      build_lt σ a k k.isLt] at hjk
    have := σ.injective hjk.1
    ext; simpa using congrArg Fin.val this
  · refine ⟨σ.symm a, ?_⟩
    rw [edge_initial, edge_last, build_lt σ a _ (σ.symm a).isLt, build_N, build_succ]
    simp
  · intro b
    refine ⟨⟨σ.symm b, by omega⟩, ?_⟩
    rw [build_lt σ a _ (σ.symm b).isLt]
    simp

private theorem build_agree {N : ℕ} {v : Fin N} {w : Walk (Fin N) (N + 1)} (h : Collision v w)
    (k : ℕ) (hk : k ≤ N) :
    build (Equiv.ofBijective (pre w) (pre_bijective h)) (w ⟨N, by omega⟩) ⟨k, by omega⟩ =
      w ⟨k, by omega⟩ := by
  rcases Nat.lt_or_ge k N with hlt | hge
  · rw [build_lt _ _ k hlt]; rfl
  · have hkN : k = N := by omega
    subst hkN
    exact build_N _ _

private theorem build_pre {N : ℕ} {v : Fin N} {w : Walk (Fin N) (N + 1)} (h : Collision v w) :
    build (Equiv.ofBijective (pre w) (pre_bijective h)) (w ⟨N, by omega⟩) = w := by
  set σ := Equiv.ofBijective (pre w) (pre_bijective h)
  funext t
  by_cases ht : t.val ≤ N
  · have := build_agree h t ht
    simpa using this
  · have htN : t = ⟨N + 1, by omega⟩ := by ext; simp; omega
    rw [htN]
    obtain ⟨i, hN, hN1⟩ := repeat_index h
    have hi : σ.symm (w ⟨N, by omega⟩) = i := by
      apply σ.injective
      rw [Equiv.apply_symm_apply]
      exact hN
    rw [build_succ, hN1]
    simp only [hi]
    exact build_agree h (i.val + 1) (by omega)

/-- Collision walks of length `m + 2` correspond to orderings starting at `v` together with a
revisit vertex. -/
private noncomputable def walkEquiv {m : ℕ} (v : Fin (m + 1)) :
    {w : Walk (Fin (m + 1)) (m + 2) // Collision v w} ≃
      {σ : Equiv.Perm (Fin (m + 1)) // σ 0 = v} × Fin (m + 1) where
  toFun w := (⟨Equiv.ofBijective (pre w.1) (pre_bijective w.2), w.2.1⟩, w.1 ⟨m + 1, by omega⟩)
  invFun x := ⟨build x.1.1 x.2, by
    have := build_collision x.1.1 x.2 (Nat.succ_pos m)
    rwa [show (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) = 0 from rfl, x.1.2] at this⟩
  left_inv w := Subtype.ext (build_pre w.2)
  right_inv x := by
    obtain ⟨⟨σ, hσ⟩, a⟩ := x
    refine Prod.ext (Subtype.ext (Equiv.ext fun i => ?_)) (build_N σ a)
    show build σ a ⟨i, by omega⟩ = σ i
    rw [build_lt σ a i i.isLt]

/-- Orderings of `Fin (m + 1)` with a fixed first vertex correspond to orderings of `Fin m`. -/
private def startEquiv {m : ℕ} (v : Fin (m + 1)) :
    {σ : Equiv.Perm (Fin (m + 1)) // σ 0 = v} ≃ Equiv.Perm (Fin m) where
  toFun σ := (Equiv.Perm.decomposeFin σ.1).2
  invFun e := ⟨Equiv.Perm.decomposeFin.symm (v, e), Equiv.Perm.decomposeFin_symm_apply_zero v e⟩
  left_inv σ := by
    obtain ⟨σ, hσ⟩ := σ
    apply Subtype.ext
    have h1 : (Equiv.Perm.decomposeFin σ).1 = v := by
      rw [← hσ]
      conv_rhs => rw [← Equiv.Perm.decomposeFin.symm_apply_apply σ]
      exact (Equiv.Perm.decomposeFin_symm_apply_zero _ _).symm
    show Equiv.Perm.decomposeFin.symm (v, (Equiv.Perm.decomposeFin σ).2) = σ
    rw [← h1]
    exact Equiv.Perm.decomposeFin.symm_apply_apply σ
  right_inv e := by
    show (Equiv.Perm.decomposeFin (Equiv.Perm.decomposeFin.symm (v, e))).2 = e
    rw [Equiv.Perm.decomposeFin.apply_symm_apply]

/-- For every `n` and start `v : Fin n`, `T(n, n + 1) = n!`. -/
theorem earliest_count (n : ℕ) (v : Fin n) : collisionCount n v (n + 1) = n.factorial := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := v.isLt; omega⟩
  classical
  have h1 : collisionCount (m + 1) v (m + 1 + 1) =
      Nat.card {e : OrderedEdges (Fin (m + 1)) v (m + 1) // SourceCollision e} := by
    rw [Nat.card_eq_fintype_card]
    simp only [collisionCount]
  rw [h1, Nat.card_congr (sourceCollisionEquiv v (m + 1)).symm, Nat.card_congr (walkEquiv v),
    Nat.card_prod, Nat.card_congr (startEquiv v), Nat.card_perm, Nat.card_eq_fintype_card,
    Fintype.card_fin, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial_succ]
  ring

end D5.S3.Combinatorics.Graph.Walks.CollisionEarliest
