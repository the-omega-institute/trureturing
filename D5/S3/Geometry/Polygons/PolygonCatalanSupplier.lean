/- GID: D5/S3/Geometry/Polygons/PolygonCatalanSupplier
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonCatalanSupplier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Licensed exact interval and polygon Catalan enumeration supplier. -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Circular.ZMod
import Mathlib.Data.Set.Card
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Prod

/-! Exact licensed count cone from AxiomMath/ClusterAlgebras at
`a9174706bce3bcb0fa342b4614f98ef2acb7f91c`. Source spans, hashes, complete
Apache-2.0 license, metadata adaptations, and receiver-pinned replacement
condition are in docs/reports/licenses/cluster-algebras-polygon-third-party.md.
The proof bodies and source declaration names are unchanged. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/

namespace ClusterAlgebras

variable {m : ℕ} [NeZero m]

/-! ### Segments, sides and diagonals -/

/-- A **segment** of the convex `m`-gon: a two-element subset of `ZMod m`, presented as an
unordered pair of distinct vertices. -/
def IsSegment (e : Sym2 (ZMod m)) : Prop := ¬e.IsDiag

/-- A segment is a **side** of the `m`-gon when its endpoints are cyclically consecutive,
that is, when it is `s(i, i + 1)` for some vertex `i`. -/
def IsSide (e : Sym2 (ZMod m)) : Prop := ∃ i : ZMod m, e = s(i, i + 1)

/-- A segment is a **diagonal** when it is not a side. -/
def IsDiagonal (e : Sym2 (ZMod m)) : Prop := IsSegment e ∧ ¬IsSide e

/-- Being a segment is decidable: it is the negation of `Sym2.IsDiag`. -/
instance instDecidablePredIsSegment : DecidablePred (IsSegment (m := m)) := fun _ => by
  unfold IsSegment; infer_instance

/-- Being a side is decidable: the witness `i` ranges over the finite type `ZMod m`. -/
instance instDecidablePredIsSide : DecidablePred (IsSide (m := m)) := fun _ => by
  unfold IsSide; infer_instance

/-- Being a diagonal is decidable. -/
instance instDecidablePredIsDiagonal : DecidablePred (IsDiagonal (m := m)) := fun _ => by
  unfold IsDiagonal; infer_instance

/-! ### Crossing -/

/-- Two segments **cross** when, naming their endpoints suitably, each of the two arcs that
`{a, b}` cuts `ZMod m` into contains one endpoint of `{c, d}`: `sbtw a c b` and `sbtw b d a`. -/
def Cross (e f : Sym2 (ZMod m)) : Prop :=
  ∃ a b c d : ZMod m, e = s(a, b) ∧ f = s(c, d) ∧ sbtw a c b ∧ sbtw b d a

/-- A **triangulation** of the convex `m`-gon: a set of pairwise non-crossing diagonals,
maximal with that property. Maximality says every diagonal outside `T` crosses some element
of `T`. -/
structure IsTriangulation (T : Finset (Sym2 (ZMod m))) : Prop where
  /-- Every element of `T` is a diagonal. -/
  isDiagonal : ∀ e ∈ T, IsDiagonal e
  /-- No two elements of `T` cross. -/
  noncrossing : ∀ e ∈ T, ∀ f ∈ T, ¬Cross e f
  /-- `T` is maximal: any diagonal outside it crosses something in it. -/
  maximal : ∀ e, IsDiagonal e → e ∉ T → ∃ f ∈ T, Cross e f

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/

namespace ClusterAlgebras

/-- The **Catalan numbers** `c_N`: `c₀ = 1` and `c_{N+1} = ∑_{i=0}^{N} cᵢ c_{N-i}`. This is
Mathlib's `catalan`, which is defined by this recurrence; see `catalanNumber_zero` and
`catalanNumber_succ`. -/
abbrev catalanNumber (N : ℕ) : ℕ :=
  catalan N

/-- `c₀ = 1`. -/
theorem catalanNumber_zero : catalanNumber 0 = 1 :=
  catalan_zero

/-- `c_{N+1} = ∑_{i=0}^{N} cᵢ c_{N-i}`. -/
theorem catalanNumber_succ (N : ℕ) :
    catalanNumber (N + 1) =
      ∑ i ∈ Finset.range (N + 1), catalanNumber i * catalanNumber (N - i) := by
  rw [catalanNumber, catalan_succ, Finset.sum_range (fun i => catalan i * catalan (N - i))]

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/

namespace ClusterAlgebras

namespace TypeA

/-! ### Interleaving, sides and diagonals -/

/-- Two two-element sets of integers `{i, j}` and `{k, l}`, given as increasing pairs `(i, j)` and
`(k, l)`, **interleave** if `i < k < j < l` or `k < i < l < j`. -/
def Interleave (p q : ℤ × ℤ) : Prop :=
  (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2) ∨ (q.1 < p.1 ∧ p.1 < q.2 ∧ q.2 < p.2)

/-- Interleaving is decidable: it is a condition on four integers. -/
instance instDecidableRelInterleave : DecidableRel Interleave := fun _ _ => by
  unfold Interleave
  infer_instance

/-- Interleaving is symmetric in its two arguments. -/
theorem Interleave.symm {p q : ℤ × ℤ} (h : Interleave p q) : Interleave q p :=
  Or.symm h

/-- The **sides** of `[a, b]`: the pairs `(i, i + 1)` with `a ≤ i < b`, and the pair `(a, b)`. -/
def intervalSides (a b : ℤ) : Finset (ℤ × ℤ) :=
  insert (a, b) ((Finset.Ico a b).image fun i => (i, i + 1))

/-- The set `D[a, b]` of **diagonals** of `[a, b]`: the increasing pairs `(i, j)` of elements of
`[a, b]` with `i + 2 ≤ j` and `(i, j) ≠ (a, b)`. -/
def intervalDiagonals (a b : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc a b ×ˢ Finset.Icc a b).filter fun p => p.1 + 2 ≤ p.2 ∧ p ≠ (a, b)

/-- A **triangulation of `[a, b]`**: a set `S ⊆ D[a, b]`, no two elements of which interleave,
such that every element of `D[a, b] \ S` interleaves some element of `S`. -/
def IsIntervalTriangulation (a b : ℤ) (S : Finset (ℤ × ℤ)) : Prop :=
  S ⊆ intervalDiagonals a b ∧ (∀ p ∈ S, ∀ q ∈ S, ¬Interleave p q) ∧
    ∀ p ∈ intervalDiagonals a b, p ∉ S → ∃ q ∈ S, Interleave p q

/-- Being a triangulation of `[a, b]` is decidable: every quantifier is bounded. -/
instance instDecidablePredIsIntervalTriangulation (a b : ℤ) :
    DecidablePred (IsIntervalTriangulation a b) := fun _ => by
  unfold IsIntervalTriangulation
  infer_instance

/-- The **segments** of a triangulation `S` of `[a, b]`: its elements and the sides of
`[a, b]`. -/
def intervalSegments (a b : ℤ) (S : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  S ∪ intervalSides a b

/-- The finite set of **triangulations of `[a, b]`**, as subsets of `D[a, b]`. -/
def intervalTriangulations (a b : ℤ) : Finset (Finset (ℤ × ℤ)) :=
  (intervalDiagonals a b).powerset.filter (IsIntervalTriangulation a b)

/-- The **number `τ(a, b)` of triangulations of `[a, b]`**. -/
def intervalTriangulationCount (a b : ℤ) : ℕ :=
  (intervalTriangulations a b).card

/-- The finite set of triangulations consists of exactly the triangulations. -/
theorem mem_intervalTriangulations {a b : ℤ} {S : Finset (ℤ × ℤ)} :
    S ∈ intervalTriangulations a b ↔ IsIntervalTriangulation a b S := by
  rw [intervalTriangulations, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

variable {a b : ℤ} {S : Finset (ℤ × ℤ)}

/-! ### Membership in the sides and the diagonals -/

/-- An increasing pair `(i, j)` is a diagonal of `[a, b]` iff `a ≤ i`, `j ≤ b`, `i + 2 ≤ j` and
`(i, j) ≠ (a, b)`. -/
theorem mk_mem_intervalDiagonals_iff {i j : ℤ} :
    (i, j) ∈ intervalDiagonals a b ↔ a ≤ i ∧ j ≤ b ∧ i + 2 ≤ j ∧ ¬(i = a ∧ j = b) := by
  simp only [intervalDiagonals, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, ne_eq,
    Prod.mk.injEq]
  omega

/-- A pair `(i, j)` is a side of `[a, b]` iff it is `(a, b)` or `(i, i + 1)` with `a ≤ i < b`. -/
theorem mk_mem_intervalSides_iff {i j : ℤ} :
    (i, j) ∈ intervalSides a b ↔ (i = a ∧ j = b) ∨ (a ≤ i ∧ i < b ∧ j = i + 1) := by
  simp only [intervalSides, Finset.mem_insert, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
  constructor
  · rintro (h | ⟨x, hx, rfl, rfl⟩)
    exacts [.inl h, .inr ⟨hx.1, hx.2, rfl⟩]
  · rintro (h | ⟨h1, h2, rfl⟩)
    exacts [.inl h, .inr ⟨i, ⟨h1, h2⟩, rfl, rfl⟩]

/-- A side of `[a, b]` interleaves no pair whose entries lie in `[a, b]`. -/
theorem not_interleave_of_mem_intervalSides {i j k l : ℤ} (hp : (i, j) ∈ intervalSides a b)
    (hk : a ≤ k) (hl : l ≤ b) : ¬Interleave (i, j) (k, l) := by
  have := mk_mem_intervalSides_iff.1 hp
  simp only [Interleave]
  omega

/-- A segment `(i, j)` of a triangulation of `[a, b]` satisfies `a ≤ i < j ≤ b`. -/
theorem IsIntervalTriangulation.bounds_of_mem_intervalSegments (hab : a < b)
    (hS : IsIntervalTriangulation a b S) {i j : ℤ} (h : (i, j) ∈ intervalSegments a b S) :
    a ≤ i ∧ i < j ∧ j ≤ b := by
  rcases Finset.mem_union.1 h with h | h
  · have := mk_mem_intervalDiagonals_iff.1 (hS.1 h)
    omega
  · have := mk_mem_intervalSides_iff.1 h
    omega

/-! ### Segments and apexes -/

/-- **No two segments of a triangulation of an interval interleave.** -/
theorem IsIntervalTriangulation.not_interleave (hab : a < b) (hS : IsIntervalTriangulation a b S)
    {p q : ℤ × ℤ} (hp : p ∈ intervalSegments a b S) (hq : q ∈ intervalSegments a b S) :
    ¬Interleave p q := by
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  have hp' := hS.bounds_of_mem_intervalSegments hab hp
  have hq' := hS.bounds_of_mem_intervalSegments hab hq
  rcases Finset.mem_union.1 hp with hp | hp
  · rcases Finset.mem_union.1 hq with hq | hq
    · exact hS.2.1 _ hp _ hq
    · exact fun h => not_interleave_of_mem_intervalSides hq hp'.1 hp'.2.2 h.symm
  · exact not_interleave_of_mem_intervalSides hp hq'.1 hq'.2.2

/-- **A two-element subset of `[a, b]` that is not a segment of a triangulation `S` interleaves
some element of `S`.** -/
theorem IsIntervalTriangulation.exists_interleave (hab : a < b)
    (hS : IsIntervalTriangulation a b S) {i j : ℤ} (hai : a ≤ i) (hij : i < j) (hjb : j ≤ b)
    (h : (i, j) ∉ intervalSegments a b S) : ∃ q ∈ S, Interleave (i, j) q := by
  refine hS.2.2 _ ?_ fun h' => h (Finset.mem_union_left _ h')
  have hs : (i, j) ∉ intervalSides a b := fun h' => h (Finset.mem_union_right _ h')
  rw [mk_mem_intervalSides_iff] at hs
  rw [mk_mem_intervalDiagonals_iff]
  omega

/-- **The apex over a segment of an interval triangulation.** If `{i, k}` is a segment of a
triangulation `S` of `[a, b]` with `k ≥ i + 2`, there is exactly one `j` with `i < j < k` such
that `{i, j}` and `{j, k}` are both segments of `S`. -/
theorem IsIntervalTriangulation.existsUnique_apex (hab : a < b)
    (hS : IsIntervalTriangulation a b S) {i k : ℤ} (hik : i + 2 ≤ k)
    (h : (i, k) ∈ intervalSegments a b S) :
    ∃! j, i < j ∧ j < k ∧ (i, j) ∈ intervalSegments a b S ∧ (j, k) ∈ intervalSegments a b S := by
  have hb := hS.bounds_of_mem_intervalSegments hab h
  have seg_of_mem : ∀ {p}, p ∈ S → p ∈ intervalSegments a b S := fun hp =>
    Finset.mem_union_left _ hp
  have side_seg : ∀ {x : ℤ}, a ≤ x → x < b → (x, x + 1) ∈ intervalSegments a b S := fun h1 h2 =>
    Finset.mem_union_right _ (mk_mem_intervalSides_iff.2 (Or.inr ⟨h1, h2, rfl⟩))
  set J := (Finset.Ioo i k).filter (fun j => (i, j) ∈ intervalSegments a b S)
  have hJne : J.Nonempty :=
    ⟨i + 1, Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 ⟨by omega, by omega⟩, side_seg hb.1 (by omega)⟩⟩
  have hjJ := Finset.max'_mem J hJne
  set j := J.max' hJne
  obtain ⟨hjIoo, hij⟩ := Finset.mem_filter.1 hjJ
  rw [Finset.mem_Ioo] at hjIoo
  have hjk : (j, k) ∈ intervalSegments a b S := by
    by_contra hjk
    rcases eq_or_lt_of_le (show j + 1 ≤ k by omega) with he | hlt
    · exact hjk (he ▸ side_seg (by omega) (by omega))
    obtain ⟨⟨p, q⟩, hpq, hint⟩ := hS.exists_interleave hab (by omega) hjIoo.2 hb.2.2 hjk
    have hpq' := mk_mem_intervalDiagonals_iff.1 (hS.1 hpq)
    have nik := hS.not_interleave hab h (seg_of_mem hpq)
    have nij := hS.not_interleave hab hij (seg_of_mem hpq)
    simp only [Interleave] at hint nik nij
    by_cases hpi : p = i
    · have hiq : (i, q) ∈ S := hpi ▸ hpq
      have := J.le_max' q (Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 (by omega), seg_of_mem hiq⟩)
      omega
    · omega
  refine ⟨j, ⟨hjIoo.1, hjIoo.2, hij, hjk⟩, ?_⟩
  rintro j' ⟨h1, h2, h3, h4⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hS.not_interleave hab hij h4 (by simp only [Interleave]; omega)
  · exact hS.not_interleave hab h3 hjk (by simp only [Interleave]; omega)

/-! ### Cutting at the apex of the base -/

/-- Every diagonal of a triangulation of `[a, b]` lies in `[a, k]` or in `[k, b]`, where `k` is an
apex over the side `{a, b}`. -/
theorem IsIntervalTriangulation.le_or_le_of_apex (hab : a < b)
    (hS : IsIntervalTriangulation a b S) {k : ℤ} (h1 : (a, k) ∈ intervalSegments a b S)
    (h2 : (k, b) ∈ intervalSegments a b S) {i j : ℤ} (h : (i, j) ∈ S) : j ≤ k ∨ k ≤ i := by
  have hd := mk_mem_intervalDiagonals_iff.1 (hS.1 h)
  have n1 := hS.not_interleave hab h1 (Finset.mem_union_left _ h)
  have n2 := hS.not_interleave hab h2 (Finset.mem_union_left _ h)
  simp only [Interleave] at n1 n2
  omega

/-- A triangulation `S` of `[a, b]` with apex `k` over `{a, b}` is the union of `S ∩ D[a, k]`,
`S ∩ D[k, b]` and those of `{a, k}`, `{k, b}` that are diagonals of `[a, b]`. -/
theorem IsIntervalTriangulation.eq_union_of_apex (hab : a < b)
    (hS : IsIntervalTriangulation a b S) {k : ℤ} (hak : a < k) (hkb : k < b)
    (h1 : (a, k) ∈ intervalSegments a b S) (h2 : (k, b) ∈ intervalSegments a b S) :
    S = S ∩ intervalDiagonals a k ∪ S ∩ intervalDiagonals k b ∪
      ({(a, k), (k, b)} ∩ intervalDiagonals a b) := by
  ext ⟨i, j⟩
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq, mk_mem_intervalDiagonals_iff]
  constructor
  · intro h
    have hd := mk_mem_intervalDiagonals_iff.1 (hS.1 h)
    have hc := hS.le_or_le_of_apex hab h1 h2 h
    by_cases hE : (i = a ∧ j = k) ∨ (i = k ∧ j = b)
    · exact Or.inr ⟨hE, hd⟩
    · rcases hc with hc | hc
      · exact Or.inl (Or.inl ⟨h, by omega⟩)
      · exact Or.inl (Or.inr ⟨h, by omega⟩)
  · rintro ((⟨h, -⟩ | ⟨h, -⟩) | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, hd⟩)
    · exact h
    · exact h
    · exact (Finset.mem_union.1 h1).resolve_right fun h => by
        rw [mk_mem_intervalSides_iff] at h
        omega
    · exact (Finset.mem_union.1 h2).resolve_right fun h => by
        rw [mk_mem_intervalSides_iff] at h
        omega

/-- Cutting at an apex `k` over `{a, b}`: `S ∩ D[a, k]` is a triangulation of `[a, k]`. -/
theorem IsIntervalTriangulation.inter_left_of_apex (hab : a < b)
    (hS : IsIntervalTriangulation a b S) {k : ℤ} (hkb : k < b)
    (h1 : (a, k) ∈ intervalSegments a b S) (h2 : (k, b) ∈ intervalSegments a b S) :
    IsIntervalTriangulation a k (S ∩ intervalDiagonals a k) := by
  refine ⟨Finset.inter_subset_right, fun p hp q hq =>
    hS.2.1 p (Finset.mem_inter.1 hp).1 q (Finset.mem_inter.1 hq).1, ?_⟩
  rintro ⟨i, j⟩ he hnot
  have he' := mk_mem_intervalDiagonals_iff.1 he
  have hnS : (i, j) ∉ S := fun h => hnot (Finset.mem_inter.2 ⟨h, he⟩)
  obtain ⟨⟨p, q⟩, hpq, hint⟩ := hS.2.2 _ (mk_mem_intervalDiagonals_iff.2 (by omega)) hnS
  have hd := mk_mem_intervalDiagonals_iff.1 (hS.1 hpq)
  have hc := hS.le_or_le_of_apex hab h1 h2 hpq
  simp only [Interleave] at hint
  refine ⟨(p, q), Finset.mem_inter.2 ⟨hpq, mk_mem_intervalDiagonals_iff.2 (by omega)⟩, ?_⟩
  simp only [Interleave]
  omega

/-- Cutting at an apex `k` over `{a, b}`: `S ∩ D[k, b]` is a triangulation of `[k, b]`. -/
theorem IsIntervalTriangulation.inter_right_of_apex (hab : a < b)
    (hS : IsIntervalTriangulation a b S) {k : ℤ} (hak : a < k)
    (h1 : (a, k) ∈ intervalSegments a b S) (h2 : (k, b) ∈ intervalSegments a b S) :
    IsIntervalTriangulation k b (S ∩ intervalDiagonals k b) := by
  refine ⟨Finset.inter_subset_right, fun p hp q hq =>
    hS.2.1 p (Finset.mem_inter.1 hp).1 q (Finset.mem_inter.1 hq).1, ?_⟩
  rintro ⟨i, j⟩ he hnot
  have he' := mk_mem_intervalDiagonals_iff.1 he
  have hnS : (i, j) ∉ S := fun h => hnot (Finset.mem_inter.2 ⟨h, he⟩)
  obtain ⟨⟨p, q⟩, hpq, hint⟩ := hS.2.2 _ (mk_mem_intervalDiagonals_iff.2 (by omega)) hnS
  have hd := mk_mem_intervalDiagonals_iff.1 (hS.1 hpq)
  have hc := hS.le_or_le_of_apex hab h1 h2 hpq
  simp only [Interleave] at hint
  refine ⟨(p, q), Finset.mem_inter.2 ⟨hpq, mk_mem_intervalDiagonals_iff.2 (by omega)⟩, ?_⟩
  simp only [Interleave]
  omega

/-- Membership in the glued set `S₁ ∪ S₂ ∪ E_k` of triangulations of `[a, k]` and `[k, b]`. -/
theorem mk_mem_union_intervalDiagonals_iff {k : ℤ} {S₁ S₂ : Finset (ℤ × ℤ)} {i j : ℤ} :
    (i, j) ∈ S₁ ∪ S₂ ∪ ({(a, k), (k, b)} ∩ intervalDiagonals a b) ↔
      (i, j) ∈ S₁ ∨ (i, j) ∈ S₂ ∨
        (((i = a ∧ j = k) ∨ (i = k ∧ j = b)) ∧ (i, j) ∈ intervalDiagonals a b) := by
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq, or_assoc]

/-- In the glued set `S₁ ∪ S₂ ∪ E_k`, every diagonal of `[a, b]` outside it interleaves one of
its elements. -/
private theorem IsIntervalTriangulation.exists_interleave_union {k : ℤ} (hak : a < k)
    (hkb : k < b) {S₁ S₂ : Finset (ℤ × ℤ)} (h1 : IsIntervalTriangulation a k S₁)
    (h2 : IsIntervalTriangulation k b S₂) :
    ∀ p ∈ intervalDiagonals a b, p ∉ S₁ ∪ S₂ ∪ ({(a, k), (k, b)} ∩ intervalDiagonals a b) →
      ∃ q ∈ S₁ ∪ S₂ ∪ ({(a, k), (k, b)} ∩ intervalDiagonals a b), Interleave p q := by
  rintro ⟨p, q⟩ he hnot
  have he' := mk_mem_intervalDiagonals_iff.1 he
  have memL : ∀ {x}, x ∈ S₁ → x ∈ S₁ ∪ S₂ ∪ ({(a, k), (k, b)} ∩ intervalDiagonals a b) :=
    fun hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have memR : ∀ {x}, x ∈ S₂ → x ∈ S₁ ∪ S₂ ∪ ({(a, k), (k, b)} ∩ intervalDiagonals a b) :=
    fun hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  by_cases hqk : q ≤ k
  · by_cases hE : p = a ∧ q = k
    · exact absurd (mk_mem_union_intervalDiagonals_iff.2 (Or.inr (Or.inr ⟨Or.inl hE, he⟩))) hnot
    · obtain ⟨f, hf, hint⟩ := h1.2.2 _ (mk_mem_intervalDiagonals_iff.2 (by omega))
        fun h => hnot (memL h)
      exact ⟨f, memL hf, hint⟩
  by_cases hkp : k ≤ p
  · by_cases hE : p = k ∧ q = b
    · exact absurd (mk_mem_union_intervalDiagonals_iff.2 (Or.inr (Or.inr ⟨Or.inr hE, he⟩))) hnot
    · obtain ⟨f, hf, hint⟩ := h2.2.2 _ (mk_mem_intervalDiagonals_iff.2 (by omega))
        fun h => hnot (memR h)
      exact ⟨f, memR hf, hint⟩
  by_cases hpa : a < p
  · refine ⟨(a, k), mk_mem_union_intervalDiagonals_iff.2 (Or.inr (Or.inr
      ⟨Or.inl ⟨rfl, rfl⟩, mk_mem_intervalDiagonals_iff.2 (by omega)⟩)), ?_⟩
    simp only [Interleave]
    omega
  · refine ⟨(k, b), mk_mem_union_intervalDiagonals_iff.2 (Or.inr (Or.inr
      ⟨Or.inr ⟨rfl, rfl⟩, mk_mem_intervalDiagonals_iff.2 (by omega)⟩)), ?_⟩
    simp only [Interleave]
    omega

/-- Gluing triangulations of `[a, k]` and `[k, b]`, together with those of `{a, k}`, `{k, b}`
that are diagonals of `[a, b]`, gives a triangulation of `[a, b]`. -/
theorem IsIntervalTriangulation.union {k : ℤ} (hak : a < k) (hkb : k < b)
    {S₁ S₂ : Finset (ℤ × ℤ)} (h1 : IsIntervalTriangulation a k S₁)
    (h2 : IsIntervalTriangulation k b S₂) :
    IsIntervalTriangulation a b (S₁ ∪ S₂ ∪ ({(a, k), (k, b)} ∩ intervalDiagonals a b)) := by
  have c1 : ∀ {i j}, (i, j) ∈ S₁ → a ≤ i ∧ j ≤ k ∧ i + 2 ≤ j ∧ ¬(i = a ∧ j = k) := fun h =>
    mk_mem_intervalDiagonals_iff.1 (h1.1 h)
  have c2 : ∀ {i j}, (i, j) ∈ S₂ → k ≤ i ∧ j ≤ b ∧ i + 2 ≤ j ∧ ¬(i = k ∧ j = b) := fun h =>
    mk_mem_intervalDiagonals_iff.1 (h2.1 h)
  refine ⟨?_, ?_, exists_interleave_union hak hkb h1 h2⟩
  · rintro ⟨i, j⟩ h
    rcases mk_mem_union_intervalDiagonals_iff.1 h with h | h | ⟨-, h⟩
    · have := c1 h
      exact mk_mem_intervalDiagonals_iff.2 (by omega)
    · have := c2 h
      exact mk_mem_intervalDiagonals_iff.2 (by omega)
    · exact h
  · rintro ⟨i, j⟩ hp ⟨l, m⟩ hq hint
    rcases mk_mem_union_intervalDiagonals_iff.1 hp with hp | hp | ⟨hp, -⟩ <;>
      rcases mk_mem_union_intervalDiagonals_iff.1 hq with hq | hq | ⟨hq, -⟩
    all_goals first
      | exact h1.2.1 _ hp _ hq hint
      | exact h2.2.1 _ hp _ hq hint
      | try have := c1 hp
        try have := c2 hp
        try have := c1 hq
        try have := c2 hq
        simp only [Interleave] at hint
        omega

/-- The glued triangulation meets `D[a, k]` in `S₁`. -/
theorem union_inter_intervalDiagonals_left {k : ℤ} {S₁ S₂ : Finset (ℤ × ℤ)}
    (h1 : IsIntervalTriangulation a k S₁) (h2 : IsIntervalTriangulation k b S₂) :
    (S₁ ∪ S₂ ∪ ({(a, k), (k, b)} ∩ intervalDiagonals a b)) ∩ intervalDiagonals a k = S₁ := by
  ext ⟨i, j⟩
  rw [Finset.mem_inter, mk_mem_union_intervalDiagonals_iff]
  constructor
  · rintro ⟨h | h | ⟨hE, -⟩, hd⟩
    · exact h
    · have := mk_mem_intervalDiagonals_iff.1 (h2.1 h)
      have := mk_mem_intervalDiagonals_iff.1 hd
      omega
    · have := mk_mem_intervalDiagonals_iff.1 hd
      omega
  · exact fun h => ⟨Or.inl h, h1.1 h⟩

/-- The glued triangulation meets `D[k, b]` in `S₂`. -/
theorem union_inter_intervalDiagonals_right {k : ℤ} (hak : a < k) {S₁ S₂ : Finset (ℤ × ℤ)}
    (h1 : IsIntervalTriangulation a k S₁) (h2 : IsIntervalTriangulation k b S₂) :
    (S₁ ∪ S₂ ∪ ({(a, k), (k, b)} ∩ intervalDiagonals a b)) ∩ intervalDiagonals k b = S₂ := by
  ext ⟨i, j⟩
  rw [Finset.mem_inter, mk_mem_union_intervalDiagonals_iff]
  constructor
  · rintro ⟨h | h | ⟨hE, -⟩, hd⟩
    · have := mk_mem_intervalDiagonals_iff.1 (h1.1 h)
      have := mk_mem_intervalDiagonals_iff.1 hd
      omega
    · exact h
    · have := mk_mem_intervalDiagonals_iff.1 hd
      omega
  · exact fun h => ⟨Or.inr (Or.inl h), h2.1 h⟩

/-- In the glued triangulation, `{a, k}` and `{k, b}` are segments. -/
theorem union_apex_mem_intervalSegments {k : ℤ} (hak : a < k) (hkb : k < b)
    {S₁ S₂ : Finset (ℤ × ℤ)} :
    (a, k) ∈ intervalSegments a b (S₁ ∪ S₂ ∪ ({(a, k), (k, b)} ∩ intervalDiagonals a b)) ∧
      (k, b) ∈ intervalSegments a b (S₁ ∪ S₂ ∪ ({(a, k), (k, b)} ∩ intervalDiagonals a b)) := by
  constructor
  · by_cases hk : k = a + 1
    · exact Finset.mem_union_right _ (mk_mem_intervalSides_iff.2 (Or.inr ⟨le_rfl, by omega, hk⟩))
    · exact Finset.mem_union_left _ (mk_mem_union_intervalDiagonals_iff.2 (Or.inr (Or.inr
        ⟨Or.inl ⟨rfl, rfl⟩, mk_mem_intervalDiagonals_iff.2 (by omega)⟩)))
  · by_cases hk : b = k + 1
    · exact Finset.mem_union_right _ (mk_mem_intervalSides_iff.2 (Or.inr ⟨by omega, hkb, hk⟩))
    · exact Finset.mem_union_left _ (mk_mem_union_intervalDiagonals_iff.2 (Or.inr (Or.inr
        ⟨Or.inr ⟨rfl, rfl⟩, mk_mem_intervalDiagonals_iff.2 (by omega)⟩)))

/-- Two triples `(k, S₁, S₂)` are equal when their apexes and their underlying sets are. -/
private theorem sigma_mk_eq_of_val_eq {k k' : Set.Ioo a b} (hk : k' = k) {U : Finset (ℤ × ℤ)}
    {t₁ : {S // IsIntervalTriangulation a k' S}} {t₂ : {S // IsIntervalTriangulation k' b S}}
    {S₁ : {S // IsIntervalTriangulation a k S}} {S₂ : {S // IsIntervalTriangulation k b S}}
    (ht₁ : t₁.1 = U ∩ intervalDiagonals a k') (ht₂ : t₂.1 = U ∩ intervalDiagonals k' b)
    (h₁ : U ∩ intervalDiagonals a k = S₁.1) (h₂ : U ∩ intervalDiagonals k b = S₂.1) :
    (⟨k', t₁, t₂⟩ : Σ k : Set.Ioo a b, {S₁ // IsIntervalTriangulation a k S₁} ×
      {S₂ // IsIntervalTriangulation k b S₂}) = ⟨k, S₁, S₂⟩ := by
  subst hk
  rw [Subtype.ext (ht₁.trans h₁), Subtype.ext (ht₂.trans h₂)]

/-- **Cutting an interval triangulation at the apex of the base.** For `b ≥ a + 2`, the map
`S ↦ (k(S), S ∩ D[a, k(S)], S ∩ D[k(S), b])`, where `k(S)` is the apex over the side `{a, b}`,
is a bijection from the triangulations of `[a, b]` onto the triples `(k, S₁, S₂)` with
`a < k < b`, `S₁` a triangulation of `[a, k]` and `S₂` one of `[k, b]`.

Stated as the existence of a bijection `e` whose first component is an apex over `{a, b}` (so
it is `k(S)`, by `IsIntervalTriangulation.existsUnique_apex`) and whose other two components
are the two intersections. -/
theorem exists_equiv_intervalTriangulation (hab : a + 2 ≤ b) :
    ∃ e : {S // IsIntervalTriangulation a b S} ≃
        Σ k : Set.Ioo a b, {S₁ // IsIntervalTriangulation a k S₁} ×
          {S₂ // IsIntervalTriangulation k b S₂},
      ∀ S, (a, ((e S).1 : ℤ)) ∈ intervalSegments a b S.1 ∧
        (((e S).1 : ℤ), b) ∈ intervalSegments a b S.1 ∧
        ((e S).2.1 : Finset (ℤ × ℤ)) = S.1 ∩ intervalDiagonals a (e S).1 ∧
        ((e S).2.2 : Finset (ℤ × ℤ)) = S.1 ∩ intervalDiagonals (e S).1 b := by
  have hab' : a < b := by omega
  have hbase : ∀ S, (a, b) ∈ intervalSegments a b S := fun S =>
    Finset.mem_union_right _ (mk_mem_intervalSides_iff.2 (Or.inl ⟨rfl, rfl⟩))
  have hex : ∀ S : {S // IsIntervalTriangulation a b S}, ∃ k : Set.Ioo a b,
      (a, (k : ℤ)) ∈ intervalSegments a b S.1 ∧ ((k : ℤ), b) ∈ intervalSegments a b S.1 := by
    intro S
    obtain ⟨k, ⟨h1, h2, h3, h4⟩, -⟩ := S.2.existsUnique_apex hab' hab (hbase S.1)
    exact ⟨⟨k, h1, h2⟩, h3, h4⟩
  choose kf hkf using hex
  let F : {S // IsIntervalTriangulation a b S} →
      Σ k : Set.Ioo a b, {S₁ // IsIntervalTriangulation a k S₁} ×
        {S₂ // IsIntervalTriangulation k b S₂} := fun S =>
    ⟨kf S, ⟨S.1 ∩ intervalDiagonals a (kf S),
        S.2.inter_left_of_apex hab' (kf S).2.2 (hkf S).1 (hkf S).2⟩,
      ⟨S.1 ∩ intervalDiagonals (kf S) b,
        S.2.inter_right_of_apex hab' (kf S).2.1 (hkf S).1 (hkf S).2⟩⟩
  have hF : Function.Bijective F := by
    constructor
    · intro S S' h
      have hk : kf S = kf S' := congrArg Sigma.fst h
      have h1 : S.1 ∩ intervalDiagonals a (kf S) = S'.1 ∩ intervalDiagonals a (kf S') :=
        congrArg (fun x => (x.2.1 : Finset (ℤ × ℤ))) h
      have h2 : S.1 ∩ intervalDiagonals (kf S) b = S'.1 ∩ intervalDiagonals (kf S') b :=
        congrArg (fun x => (x.2.2 : Finset (ℤ × ℤ))) h
      have e1 := S.2.eq_union_of_apex hab' (kf S).2.1 (kf S).2.2 (hkf S).1 (hkf S).2
      have e2 := S'.2.eq_union_of_apex hab' (kf S').2.1 (kf S').2.2 (hkf S').1 (hkf S').2
      apply Subtype.ext
      rw [e1, e2, h1, h2, hk]
    · rintro ⟨k, S₁, S₂⟩
      have hT := IsIntervalTriangulation.union k.2.1 k.2.2 S₁.2 S₂.2
      refine ⟨⟨_, hT⟩, ?_⟩
      have hk : kf ⟨_, hT⟩ = k := by
        obtain ⟨j, -, huniq⟩ := hT.existsUnique_apex hab' hab (hbase _)
        have h0 := hkf ⟨_, hT⟩
        have hu := union_apex_mem_intervalSegments (S₁ := S₁.1) (S₂ := S₂.1) k.2.1 k.2.2
        apply Subtype.ext
        rw [huniq _ ⟨(kf _).2.1, (kf _).2.2, h0.1, h0.2⟩, huniq _ ⟨k.2.1, k.2.2, hu.1, hu.2⟩]
      exact sigma_mk_eq_of_val_eq hk rfl rfl (union_inter_intervalDiagonals_left S₁.2 S₂.2)
        (union_inter_intervalDiagonals_right k.2.1 S₁.2 S₂.2)
  exact ⟨Equiv.ofBijective F hF, fun S => ⟨(hkf S).1, (hkf S).2, rfl, rfl⟩⟩

/-- The triangulations of `[a, b]` form a finite type, enumerated by
`intervalTriangulations a b`. -/
instance instFintypeSubtypeIsIntervalTriangulation (a b : ℤ) :
    Fintype {S // IsIntervalTriangulation a b S} :=
  Fintype.ofFinset (intervalTriangulations a b) fun _ => mem_intervalTriangulations

/-- `τ(a, b)` is the cardinality of the type of triangulations of `[a, b]`. -/
theorem card_subtype_isIntervalTriangulation (a b : ℤ) :
    Fintype.card {S // IsIntervalTriangulation a b S} = intervalTriangulationCount a b :=
  Fintype.card_ofFinset _ _

/-- **The recursion for `τ`**: for `b ≥ a + 2`,
`τ(a, b) = ∑_{k = a+1}^{b-1} τ(a, k) τ(k, b)`. -/
theorem intervalTriangulationCount_eq_sum (hab : a + 2 ≤ b) :
    intervalTriangulationCount a b =
      ∑ k ∈ Finset.Ioo a b, intervalTriangulationCount a k * intervalTriangulationCount k b := by
  obtain ⟨e, -⟩ := exists_equiv_intervalTriangulation hab
  rw [← card_subtype_isIntervalTriangulation, Fintype.card_congr e, Fintype.card_sigma]
  simp_rw [Fintype.card_prod, card_subtype_isIntervalTriangulation]
  exact (Finset.sum_subtype (p := fun x => x ∈ Set.Ioo a b) (Finset.Ioo a b)
    (fun _ => by rw [Finset.mem_Ioo, Set.mem_Ioo])
    fun k => intervalTriangulationCount a k * intervalTriangulationCount k b).symm

/-- `[a, a + 1]` has exactly one triangulation, the empty one. -/
theorem intervalTriangulationCount_self_add_one (a : ℤ) :
    intervalTriangulationCount a (a + 1) = 1 := by
  have hD : intervalDiagonals a (a + 1) = ∅ := by
    ext ⟨i, j⟩
    simp only [mk_mem_intervalDiagonals_iff, Finset.notMem_empty, iff_false]
    omega
  have h0 : IsIntervalTriangulation a (a + 1) ∅ :=
    ⟨Finset.empty_subset _, by simp, by simp [hD]⟩
  rw [intervalTriangulationCount, intervalTriangulations, hD, Finset.powerset_empty,
    Finset.filter_singleton, if_pos h0, Finset.card_singleton]

/-- **Triangulations of an interval are counted by the Catalan numbers**: for `a < b`,
`τ(a, b) = c_{b-a-1}`. -/
theorem intervalTriangulationCount_eq_catalanNumber (hab : a < b) :
    intervalTriangulationCount a b = catalanNumber (b - a - 1).toNat := by
  suffices H : ∀ n : ℕ, ∀ a b : ℤ, b - a - 1 = n →
      intervalTriangulationCount a b = catalanNumber n from H _ a b (by omega)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn
  rcases n with _ | n
  · obtain rfl : b = a + 1 := by omega
    rw [intervalTriangulationCount_self_add_one, catalanNumber_zero]
  · rw [intervalTriangulationCount_eq_sum (by omega), catalanNumber_succ]
    refine Finset.sum_nbij' (fun k => (k - a - 1).toNat) (fun i => a + 1 + i) ?_ ?_ ?_ ?_ ?_ <;>
      intro k hk <;> simp only [Finset.mem_Ioo, Finset.mem_range] at hk ⊢
    any_goals omega
    rw [ih (k - a - 1).toNat (by omega) a k (by omega),
      ih (n - (k - a - 1).toNat) (by omega) k b (by omega)]

end TypeA

end ClusterAlgebras

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/

namespace ClusterAlgebras

namespace TypeA

variable {m : ℕ} [NeZero m]

/-! ### Reading the polygon from a base point -/

/-- The **position** `d_c(v) ∈ [0, m-1]` of the vertex `v` read from the base point `c`: the
representative of `v - c`. -/
def basePos (c v : ZMod m) : ℤ :=
  ((v - c).val : ℤ)

/-- The image `d_c(σ)` of a segment `σ = {u, v}`: the pair of positions of its endpoints,
listed increasingly. -/
def basePosSeg (c : ZMod m) (σ : Sym2 (ZMod m)) : ℤ × ℤ :=
  Sym2.lift ⟨fun u v => (min (basePos c u) (basePos c v), max (basePos c u) (basePos c v)),
    fun _ _ => Prod.ext (min_comm _ _) (max_comm _ _)⟩ σ

/-- The image `d_c(T) = {d_c(σ) : σ ∈ T}` of a set of segments. -/
def basePosTri (c : ZMod m) (T : Finset (Sym2 (ZMod m))) : Finset (ℤ × ℤ) :=
  T.image (basePosSeg c)

omit [NeZero m] in
/-- The image of a segment, unfolded. -/
@[simp]
theorem basePosSeg_mk (c u v : ZMod m) :
    basePosSeg c s(u, v) = (min (basePos c u) (basePos c v), max (basePos c u) (basePos c v)) :=
  rfl

omit [NeZero m] in
/-- The position of a vertex is nonnegative. -/
theorem basePos_nonneg (c v : ZMod m) : 0 ≤ basePos c v := by
  unfold basePos; positivity

/-- The position of a vertex is less than `m`. -/
theorem basePos_lt (c v : ZMod m) : basePos c v < m := by
  unfold basePos; exact_mod_cast ZMod.val_lt _

/-- The position of `v` read from `c`, in terms of the representatives of `v` and `c`. -/
theorem basePos_eq_ite (c v : ZMod m) :
    basePos c v = if c.val ≤ v.val then (v.val : ℤ) - c.val else (v.val : ℤ) - c.val + m := by
  unfold basePos
  split_ifs with h
  · rw [ZMod.val_sub h]; push_cast [h]; ring
  · have hv : v - c + c = v := by ring
    have h1 : m ≤ (v - c).val + c.val := by
      by_contra h2
      have := ZMod.val_add_of_lt (not_le.mp h2)
      rw [hv] at this
      omega
    have := ZMod.val_add_of_le h1
    rw [hv] at this
    have := ZMod.val_lt (v - c)
    omega

/-- Reading from a base point is injective. -/
theorem basePos_injective (c : ZMod m) : Function.Injective (basePos c) := by
  intro u v h
  rw [basePos_eq_ite, basePos_eq_ite] at h
  have hu := ZMod.val_lt u
  have hv := ZMod.val_lt v
  apply ZMod.val_injective
  split_ifs at h <;> omega

omit [NeZero m] in
/-- Every integer of `[0, m-1]` is the position of some vertex. -/
theorem exists_basePos_eq (c : ZMod m) {k : ℤ} (h0 : 0 ≤ k) (hk : k < m) :
    ∃ v, basePos c v = k := by
  refine ⟨c + ((k.toNat : ℕ) : ZMod m), ?_⟩
  unfold basePos
  rw [add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Circular betweenness in `ZMod m`, read on representatives. -/
theorem sbtw_iff_val : ∀ x y z : ZMod m, sbtw x y z ↔ (x.val < y.val ∧ y.val < z.val) ∨
    (y.val < z.val ∧ z.val < x.val) ∨ (z.val < x.val ∧ x.val < y.val) := by
  match m, ‹NeZero m› with
  | (k + 1), _ => exact fun _ _ _ => Fin.sbtw_iff

/-- Circular betweenness of vertices is circular betweenness of their positions, read from any
base point. -/
theorem sbtw_iff_sbtw_basePos (c u x v : ZMod m) :
    sbtw u x v ↔ sbtw (basePos c u) (basePos c x) (basePos c v) := by
  rw [sbtw_iff_val, Int.sbtw_iff, basePos_eq_ite, basePos_eq_ite, basePos_eq_ite]
  have hu := ZMod.val_lt u
  have hx := ZMod.val_lt x
  have hv := ZMod.val_lt v
  split_ifs <;> omega

/-- The position of the successor `u + 1` of `u`. -/
theorem basePos_add_one (c u : ZMod m) :
    basePos c (u + 1) = if basePos c u + 1 = m then 0 else basePos c u + 1 := by
  unfold basePos
  rw [show u + 1 - c = (u - c) + 1 by ring]
  have hl := ZMod.val_lt (u - c)
  rcases Nat.lt_or_ge m 2 with hm | hm
  · obtain rfl : m = 1 := by have := NeZero.ne m; omega
    have h0 : ∀ w : ZMod 1, w.val = 0 := fun w => by have := ZMod.val_lt w; omega
    simp [h0]
  · haveI : Fact (1 < m) := ⟨hm⟩
    rcases Nat.lt_or_ge ((u - c).val + 1) m with h | h
    · rw [ZMod.val_add_of_lt (by rwa [ZMod.val_one]), ZMod.val_one, if_neg (by omega)]
      push_cast; rfl
    · rw [ZMod.val_add_of_le (by rwa [ZMod.val_one]), ZMod.val_one, if_pos (by omega)]
      omega

/-- The image of a segment determines the segment. -/
theorem basePosSeg_injective (c : ZMod m) : Function.Injective (basePosSeg c) := by
  intro σ τ h
  induction σ using Sym2.ind with | _ u v => ?_
  induction τ using Sym2.ind with | _ x y => ?_
  rw [basePosSeg_mk, basePosSeg_mk, Prod.mk.injEq] at h
  have hi := basePos_injective c
  rcases le_total (basePos c u) (basePos c v) with h1 | h1 <;>
    rcases le_total (basePos c x) (basePos c y) with h2 | h2
  · rw [min_eq_left h1, max_eq_right h1, min_eq_left h2, max_eq_right h2] at h
    rw [hi h.1, hi h.2]
  · rw [min_eq_left h1, max_eq_right h1, min_eq_right h2, max_eq_left h2] at h
    rw [hi h.1, hi h.2, Sym2.eq_swap]
  · rw [min_eq_right h1, max_eq_left h1, min_eq_left h2, max_eq_right h2] at h
    rw [hi h.1, hi h.2, Sym2.eq_swap]
  · rw [min_eq_right h1, max_eq_left h1, min_eq_right h2, max_eq_left h2] at h
    rw [hi h.1, hi h.2]

/-- A segment can be named `s(u, v)` with `d_c(u) < d_c(v)`. -/
theorem IsSegment.exists_basePos_lt (c : ZMod m) {σ : Sym2 (ZMod m)} (hσ : IsSegment σ) :
    ∃ u v, σ = s(u, v) ∧ basePos c u < basePos c v := by
  induction σ using Sym2.ind with | _ u v => ?_
  have huv : u ≠ v := by simpa [IsSegment, Sym2.mk_isDiag_iff] using hσ
  rcases lt_or_gt_of_ne ((basePos_injective c).ne huv) with h | h
  exacts [⟨u, v, rfl, h⟩, ⟨v, u, Sym2.eq_swap, h⟩]

omit [NeZero m] in
/-- For `d_c(u) < d_c(v)`, the image of `s(u, v)` is `(d_c(u), d_c(v))`. -/
theorem basePosSeg_mk_of_lt {c u v : ZMod m} (h : basePos c u < basePos c v) :
    basePosSeg c s(u, v) = (basePos c u, basePos c v) := by
  rw [basePosSeg_mk, min_eq_left h.le, max_eq_right h.le]

omit [NeZero m] in
/-- `s(u, v)` is a side exactly when `v = u + 1` or `u = v + 1`. -/
theorem isSide_mk_iff {u v : ZMod m} : IsSide s(u, v) ↔ v = u + 1 ∨ u = v + 1 := by
  constructor
  · rintro ⟨i, hi⟩
    rcases Sym2.eq_iff.1 hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [Or.inl rfl, Or.inr rfl]
  · rintro (rfl | rfl)
    exacts [⟨u, rfl⟩, ⟨v, Sym2.eq_swap⟩]

omit [NeZero m] in
/-- `s(u, v)` and `s(x, y)` cross exactly when one of `x`, `y` lies strictly between `u` and
`v` and the other strictly between `v` and `u`. -/
theorem cross_mk_iff {u v x y : ZMod m} :
    Cross s(u, v) s(x, y) ↔ (sbtw u x v ∧ sbtw v y u) ∨ (sbtw u y v ∧ sbtw v x u) := by
  constructor
  · rintro ⟨a, b, c, d, h1, h2, h3, h4⟩
    rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases Sym2.eq_iff.1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    exacts [⟨u, v, x, y, rfl, rfl, h1, h2⟩, ⟨u, v, y, x, rfl, Sym2.eq_swap, h1, h2⟩]

/-- Crossing of `s(u, v)` and `s(x, y)`, read on the positions from a base point. -/
theorem cross_mk_iff_basePos (c : ZMod m) {u v x y : ZMod m} :
    Cross s(u, v) s(x, y) ↔
      (sbtw (basePos c u) (basePos c x) (basePos c v) ∧
          sbtw (basePos c v) (basePos c y) (basePos c u)) ∨
        (sbtw (basePos c u) (basePos c y) (basePos c v) ∧
          sbtw (basePos c v) (basePos c x) (basePos c u)) := by
  simp only [cross_mk_iff, ← sbtw_iff_sbtw_basePos]

/-- For `d_c(u) < d_c(v)`, `{u, v}` is a side exactly when `d_c(v) = d_c(u) + 1` or
`(d_c(u), d_c(v)) = (0, m-1)`; this needs no bound on `m`. -/
theorem isSide_mk_iff_basePos {c u v : ZMod m} (huv : basePos c u < basePos c v) :
    IsSide s(u, v) ↔
      basePos c v = basePos c u + 1 ∨ (basePos c u = 0 ∧ basePos c v = (m : ℤ) - 1) := by
  have hi := basePos_injective c
  rw [isSide_mk_iff]
  constructor
  · rintro (rfl | rfl)
    · rw [basePos_add_one] at huv ⊢
      have := basePos_nonneg c u
      split_ifs at huv ⊢ <;> omega
    · rw [basePos_add_one] at huv ⊢
      have := basePos_lt c v
      have := basePos_nonneg c v
      split_ifs at huv ⊢ <;> omega
  · rintro (h | ⟨h1, h2⟩)
    · exact .inl (hi (by rw [basePos_add_one, if_neg (by have := basePos_lt c v; omega), h]))
    · exact .inr (hi (by rw [basePos_add_one, if_pos (by omega), h1]))

/-- `σ ↦ d_c(σ)` maps the diagonals of the `m`-gon bijectively onto `D[0, m-1]`. -/
theorem bijOn_basePosSeg_isDiagonal (c : ZMod m) :
    Set.BijOn (basePosSeg c) {σ | IsDiagonal σ} ↑(intervalDiagonals 0 ((m : ℤ) - 1)) := by
  refine ⟨?_, (basePosSeg_injective c).injOn, ?_⟩
  · intro σ hσ
    obtain ⟨u, v, rfl, huv⟩ := IsSegment.exists_basePos_lt c hσ.1
    have hs := (isSide_mk_iff_basePos huv).not.1 hσ.2
    have := basePos_nonneg c u
    have := basePos_lt c v
    simp only [Finset.mem_coe, intervalDiagonals, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc, basePosSeg_mk_of_lt huv, ne_eq, Prod.mk.injEq]
    omega
  · intro q hq
    simp only [Finset.mem_coe, intervalDiagonals, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc, ne_eq] at hq
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩ := hq
    obtain ⟨u, hu⟩ := exists_basePos_eq c h1 (by omega)
    obtain ⟨v, hv⟩ := exists_basePos_eq c h3 (by omega)
    have huv : basePos c u < basePos c v := by omega
    refine ⟨s(u, v), ⟨?_, ?_⟩, ?_⟩
    · rintro h
      rw [Sym2.mk_isDiag_iff] at h
      subst h
      omega
    · rw [isSide_mk_iff_basePos huv, hu, hv]
      rintro (h | ⟨h, h'⟩)
      · omega
      · exact h6 (Prod.ext h h')
    · rw [basePosSeg_mk_of_lt huv, hu, hv]

/-- Two segments cross exactly when their images interleave. -/
theorem cross_iff_interleave (c : ZMod m) {σ τ : Sym2 (ZMod m)} (hσ : IsSegment σ)
    (hτ : IsSegment τ) : Cross σ τ ↔ Interleave (basePosSeg c σ) (basePosSeg c τ) := by
  obtain ⟨u, v, rfl, huv⟩ := IsSegment.exists_basePos_lt c hσ
  obtain ⟨x, y, rfl, hxy⟩ := IsSegment.exists_basePos_lt c hτ
  rw [cross_mk_iff_basePos c, basePosSeg_mk_of_lt huv, basePosSeg_mk_of_lt hxy, Interleave,
    Int.sbtw_iff, Int.sbtw_iff, Int.sbtw_iff, Int.sbtw_iff]
  simp only
  omega

/-- `T ↦ d_c(T)` is a bijection from the triangulations of the convex `m`-gon onto the
triangulations of `[0, m-1]`. -/
theorem bijOn_basePosTri (c : ZMod m) :
    Set.BijOn (basePosTri c) {T | IsTriangulation T}
      {S | IsIntervalTriangulation 0 ((m : ℤ) - 1) S} := by
  classical
  have hD := bijOn_basePosSeg_isDiagonal c
  refine ⟨?_, (Finset.image_injective (basePosSeg_injective c)).injOn, ?_⟩
  · intro T hT
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hq
      exact hD.mapsTo (hT.isDiagonal σ hσ)
    · intro q hq r hr hqr
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hq
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hr
      exact hT.noncrossing σ hσ τ hτ
        ((cross_iff_interleave c (hT.isDiagonal σ hσ).1 (hT.isDiagonal τ hτ).1).2 hqr)
    · intro q hq hqT
      obtain ⟨σ, hσ, rfl⟩ := hD.surjOn hq
      have hσT : σ ∉ T := fun h => hqT (Finset.mem_image_of_mem _ h)
      obtain ⟨τ, hτ, hστ⟩ := hT.maximal σ hσ hσT
      exact ⟨basePosSeg c τ, Finset.mem_image_of_mem _ hτ,
        (cross_iff_interleave c hσ.1 (hT.isDiagonal τ hτ).1).1 hστ⟩
  · intro S hS
    refine ⟨Finset.univ.filter fun σ => IsDiagonal σ ∧ basePosSeg c σ ∈ S, ?_, ?_⟩
    · refine ⟨fun σ hσ => (Finset.mem_filter.1 hσ).2.1, ?_, ?_⟩
      · intro σ hσ τ hτ hστ
        have hσ' := (Finset.mem_filter.1 hσ).2
        have hτ' := (Finset.mem_filter.1 hτ).2
        exact hS.2.1 _ hσ'.2 _ hτ'.2 ((cross_iff_interleave c hσ'.1.1 hτ'.1.1).1 hστ)
      · intro σ hσ hσT
        have hσS : basePosSeg c σ ∉ S := fun h =>
          hσT (Finset.mem_filter.2 ⟨Finset.mem_univ _, hσ, h⟩)
        obtain ⟨q, hq, hσq⟩ := hS.2.2 _ (hD.mapsTo hσ) hσS
        obtain ⟨τ, hτ, rfl⟩ := hD.surjOn (hS.1 hq)
        exact ⟨τ, Finset.mem_filter.2 ⟨Finset.mem_univ _, hτ, hq⟩,
          (cross_iff_interleave c hσ.1 hτ.1).2 hσq⟩
    · ext q
      simp only [basePosTri, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun ⟨σ, ⟨_, hσ⟩, h⟩ => h ▸ hσ, fun hq => ?_⟩
      obtain ⟨σ, hσ, rfl⟩ := hD.surjOn (hS.1 hq)
      exact ⟨σ, ⟨hσ, hq⟩, rfl⟩


end TypeA
end ClusterAlgebras

namespace ClusterAlgebras.TypeA
variable {m : ℕ} [NeZero m]

/-- **The number of triangulations**: for `m ≥ 3` the convex `m`-gon has exactly `c_{m-2}`
triangulations. -/
theorem encard_setOf_isTriangulation (hm : 3 ≤ m) :
    {T : Finset (Sym2 (ZMod m)) | IsTriangulation T}.encard = catalanNumber (m - 2) := by
  have hbij := bijOn_basePosTri (0 : ZMod m)
  have hset : {S | IsIntervalTriangulation 0 ((m : ℤ) - 1) S} =
      ↑(intervalTriangulations 0 ((m : ℤ) - 1)) := by
    ext S
    simp [mem_intervalTriangulations]
  rw [← hbij.injOn.encard_image, hbij.image_eq, hset, Set.encard_coe_eq_coe_finsetCard,
    ← intervalTriangulationCount, intervalTriangulationCount_eq_catalanNumber (by omega)]
  congr
  omega


end ClusterAlgebras.TypeA
