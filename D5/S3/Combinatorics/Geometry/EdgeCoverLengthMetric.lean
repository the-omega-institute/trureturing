/- GID: D5/S3/Combinatorics/Geometry/EdgeCoverLengthMetric
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Geometry/EdgeCoverLengthMetric
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Constant lengths on disjoint spanning covers give center {0, a_i} and those edges. -/

import D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges

/-! The prescribed-distance realization, equation (1) of H. Ma and W. Zhang
(DOI 10.5281/zenodo.24369118, Section 2), which uses the narrow-band principle of O. Dovgoshey and
O. Rovenska (arXiv:2610.11596, proof of Theorem 3.8, formula (19)). On the vertices of `K_n`,
`n ≥ 3`, take edge-disjoint spanning edge covers `F_1, …, F_s`, give every edge of `F_i` the length
`a_i`, and give every remaining edge its own length, different from all `a_i`; all lengths lie in a
band `[c, 2c]` with `c > 0`. The source takes the half-open band `[1, 2)` and distinct `a_i`; the
closed band and the absence of a distinctness condition make the statement more general. This is a
metric with center `{0, a_1, …, a_s}` and central edge set `F_1 ∪ ⋯ ∪ F_s`, for the center and
central graph of `DovgosheyRovenskaCentralEdges`.

admission_basis: escape-witness. Escape witnesses: ldist_tri with the metric on `LSpace` (any two
lengths in the band sum to at least the third), mem_center (each `a_i` is central because `F_i`
covers every vertex, and a length used on a single edge misses a third vertex), central_adj (the
central edges are exactly the class edges). -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Geometry.EdgeCoverLengthMetric

open D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges


/-- Edge-disjoint spanning edge covers `F i` of `K_n`, class lengths `a i`, and lengths `len` on
the remaining edges, pairwise distinct and different from every `a i`, all in the band `[c, 2c]`
for some `c > 0`. Values of `len` on the diagonal and on class edges are not used. -/
structure LengthData (n s : ℕ) where
  c : ℝ
  c_pos : 0 < c
  F : Fin s → SimpleGraph (Fin n)
  disjoint : ∀ i j, i ≠ j → Disjoint (F i) (F j)
  cover : ∀ i (x : Fin n), ∃ y, (F i).Adj x y
  a : Fin s → ℝ
  a_mem : ∀ i, c ≤ a i ∧ a i ≤ 2 * c
  len : Sym2 (Fin n) → ℝ
  len_mem : ∀ x y : Fin n, x ≠ y → (∀ i, ¬ (F i).Adj x y) → c ≤ len s(x, y) ∧ len s(x, y) ≤ 2 * c
  len_ne : ∀ x y : Fin n, x ≠ y → (∀ i, ¬ (F i).Adj x y) → ∀ i, len s(x, y) ≠ a i
  len_inj : ∀ x y z w : Fin n, x ≠ y → z ≠ w → (∀ i, ¬ (F i).Adj x y) → (∀ i, ¬ (F i).Adj z w) →
    len s(x, y) = len s(z, w) → s(x, y) = s(z, w)

variable {n s : ℕ} (D : LengthData n s)

open Classical in
/-- The prescribed distance. -/
private def ldist (x y : Fin n) : ℝ :=
  if x = y then 0 else if h : ∃ i, (D.F i).Adj x y then D.a h.choose else D.len s(x, y)

private theorem class_unique {x y : Fin n} {i j : Fin s} (hi : (D.F i).Adj x y)
    (hj : (D.F j).Adj x y) :
    i = j := by
  by_contra h
  have hd := disjoint_iff.mp (D.disjoint i j h)
  have : (D.F i ⊓ D.F j).Adj x y := ⟨hi, hj⟩
  rw [hd] at this
  exact this

private theorem ldist_class {x y : Fin n} {i : Fin s} (hi : (D.F i).Adj x y) :
    ldist D x y = D.a i := by
  have hxy : x ≠ y := hi.ne
  have hex : ∃ i, (D.F i).Adj x y := ⟨i, hi⟩
  unfold ldist
  split_ifs with h1
  · exact absurd h1 hxy
  · rw [class_unique D hex.choose_spec hi]

private theorem ldist_other {x y : Fin n} (hxy : x ≠ y) (h : ∀ i, ¬ (D.F i).Adj x y) :
    ldist D x y = D.len s(x, y) := by
  have hex : ¬ ∃ i, (D.F i).Adj x y := fun ⟨i, hi⟩ => h i hi
  unfold ldist
  split_ifs with h1
  · exact absurd h1 hxy
  · rfl

private theorem ldist_self (x : Fin n) : ldist D x x = 0 := by simp [ldist]

private theorem ldist_comm (x y : Fin n) : ldist D x y = ldist D y x := by
  by_cases hxy : x = y
  · rw [hxy]
  by_cases h : ∃ i, (D.F i).Adj x y
  · obtain ⟨i, hi⟩ := h
    rw [ldist_class D hi, ldist_class D hi.symm]
  · push Not at h
    rw [ldist_other D hxy h, ldist_other D (Ne.symm hxy) fun i hi => h i hi.symm, Sym2.eq_swap]

private theorem ldist_mem {x y : Fin n} (hxy : x ≠ y) :
    D.c ≤ ldist D x y ∧ ldist D x y ≤ 2 * D.c := by
  by_cases h : ∃ i, (D.F i).Adj x y
  · obtain ⟨i, hi⟩ := h; rw [ldist_class D hi]; exact D.a_mem i
  · push Not at h; rw [ldist_other D hxy h]; exact D.len_mem _ _ hxy h

/-- The vertices of `K_n` with the prescribed distances. -/
@[ext] structure LSpace (_D : LengthData n s) where
  pt : Fin n

private theorem ldist_tri (x y z : Fin n) : ldist D x z ≤ ldist D x y + ldist D y z := by
  by_cases hxz : x = z
  · subst hxz; rw [ldist_self]
    by_cases hxy : x = y
    · subst hxy; simp [ldist_self]
    · have := ldist_mem D hxy; have := ldist_mem D (Ne.symm hxy); have := D.c_pos
      linarith
  · have h1 := (ldist_mem D hxz).2
    by_cases hxy : x = y
    · subst hxy; rw [ldist_self, zero_add]
    by_cases hyz : y = z
    · subst hyz; rw [ldist_self, add_zero]
    have := (ldist_mem D hxy).1; have := (ldist_mem D hyz).1
    linarith

instance : MetricSpace (LSpace D) where
  dist x y := ldist D x.pt y.pt
  dist_self x := ldist_self D x.pt
  dist_comm x y := ldist_comm D x.pt y.pt
  dist_triangle x y z := ldist_tri D x.pt y.pt z.pt
  eq_of_dist_eq_zero {x y} h := by
    refine LSpace.ext ?_
    by_contra hxy
    have := (ldist_mem D hxy).1; have := D.c_pos
    change ldist D x.pt y.pt = 0 at h
    linarith

private theorem dist_eq (x y : LSpace D) : dist x y = ldist D x.pt y.pt := rfl

private theorem exists_third (hn : 3 ≤ n) (y p : Fin n) : ∃ z, z ≠ y ∧ z ≠ p := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {y, p} := fun z _ => by
    by_cases hz : z = y
    · simp [hz]
    · simp [h z hz]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at this
  have := Finset.card_le_two (a := y) (b := p)
  omega

private theorem mem_center (hn : 3 ≤ n) (t : ℝ) :
    t ∈ center (LSpace D) ↔ t = 0 ∨ t ∈ Set.range D.a := by
  constructor
  · rintro ⟨-, h⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨ht0, hta⟩ := hcon
    have hnot : ∀ (u v : Fin n), ldist D u v = t → u ≠ v ∧ (∀ i, ¬ (D.F i).Adj u v) ∧
        ldist D u v = D.len s(u, v) := by
      intro u v huv
      have hne : u ≠ v := by rintro rfl; rw [ldist_self] at huv; exact ht0 huv.symm
      have hcl : ∀ i, ¬ (D.F i).Adj u v := fun i hi =>
        hta ⟨i, by rw [← huv, ldist_class D hi]⟩
      exact ⟨hne, hcl, ldist_other D hne hcl⟩
    let p : Fin n := ⟨0, by omega⟩
    obtain ⟨y, hy⟩ := h ⟨p⟩
    obtain ⟨hyp, hycl, hylen⟩ := hnot y.pt p hy
    obtain ⟨z, hzy, hzp⟩ := exists_third hn y.pt p
    obtain ⟨w, hw⟩ := h ⟨z⟩
    obtain ⟨hwz, hwcl, hwlen⟩ := hnot w.pt z hw
    have heq : D.len s(w.pt, z) = D.len s(y.pt, p) := by
      rw [← hwlen, ← hylen]; exact hw.trans hy.symm
    have := D.len_inj _ _ _ _ hwz hyp hwcl hycl heq
    have hz : z ∈ s(y.pt, p) := this ▸ Sym2.mem_mk_right _ _
    rcases Sym2.mem_iff.mp hz with h1 | h1
    · exact hzy h1
    · exact hzp h1
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨le_rfl, fun p => ⟨p, dist_self p⟩⟩
    · refine ⟨by linarith [(D.a_mem i).1, D.c_pos], fun p => ?_⟩
      obtain ⟨y, hy⟩ := D.cover i p.pt
      exact ⟨⟨y⟩, by rw [dist_eq, ldist_class D hy.symm]⟩

private theorem center_eq (hn : 3 ≤ n) : center (LSpace D) = insert 0 (Set.range D.a) := by
  ext t; rw [mem_center D hn]; rfl

private theorem central_adj (hn : 3 ≤ n) (x y : LSpace D) :
    (centralGraph (LSpace D)).Adj x y ↔ ∃ i, (D.F i).Adj x.pt y.pt := by
  simp only [centralGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hxy, h⟩
    have hne : x.pt ≠ y.pt := fun h' => hxy (LSpace.ext h')
    have h' : dist x y ∈ center (LSpace D) := by
      rcases h with h | h
      · exact h
      · rwa [dist_comm]
    rcases (mem_center D hn _).mp h' with h0 | ⟨i, hi⟩
    · exact absurd h0 (dist_ne_zero.mpr hxy)
    · by_contra hcl
      push Not at hcl
      rw [dist_eq, ldist_other D hne hcl] at hi
      exact D.len_ne _ _ hne hcl i hi.symm
  · rintro ⟨i, hi⟩
    refine ⟨fun h => hi.ne (congrArg LSpace.pt h), Or.inl ?_⟩
    rw [dist_eq, ldist_class D hi, mem_center D hn]
    exact Or.inr ⟨i, rfl⟩

/-- Equation (1) of Ma–Zhang (DOI 10.5281/zenodo.24369118): for `n ≥ 3` the prescribed lengths
form a metric on the vertices of `K_n` with the prescribed distances, center `{0, a_1, …, a_s}`
and central edges exactly the edges of `F_1 ∪ ⋯ ∪ F_s`. -/
theorem result (hn : 3 ≤ n) :
    (∀ (x y : LSpace D) (i : Fin s), (D.F i).Adj x.pt y.pt → dist x y = D.a i) ∧
      (∀ x y : LSpace D, x ≠ y → (∀ i, ¬ (D.F i).Adj x.pt y.pt) →
        dist x y = D.len s(x.pt, y.pt)) ∧
      center (LSpace D) = insert 0 (Set.range D.a) ∧
      ∀ x y : LSpace D, (centralGraph (LSpace D)).Adj x y ↔ ∃ i, (D.F i).Adj x.pt y.pt :=
  ⟨fun x y i hi => by rw [dist_eq, ldist_class D hi],
    fun x y hxy hcl => by
      rw [dist_eq, ldist_other D (fun h => hxy (LSpace.ext h)) hcl],
    center_eq D hn, central_adj D hn⟩

end D5.S3.Combinatorics.Geometry.EdgeCoverLengthMetric
