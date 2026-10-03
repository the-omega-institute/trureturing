/- GID: D5/S3/Arith/AbsoluteValues/Heights/SuccessiveMinima
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/SuccessiveMinima
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Successive minima yield linearly independent lattice points in dilated convex bodies. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers

public section

open Metric Module MeasureTheory Set

open scoped Pointwise Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E}

namespace ZLattice

variable {i : ℕ}

/-- The `i`-th **successive minimum** of a set `B` with respect to a lattice `L`: the least
dilation of `B` containing `i + 1` linearly independent points of `L`. The case `i = 0` is the
quantity bounded by Minkowski's convex-body theorem. For `i ≥ finrank ℝ E` there is no such
family and the value is `sInf ∅ = 0`, so every statement about the minima carries
`i < finrank ℝ E`. -/
@[expose] noncomputable def successiveMinimum (L : Submodule ℤ E) (B : Set E) (i : ℕ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ ∃ v : Fin (i + 1) → E,
    (∀ j, v j ∈ (t • B) ∩ (L : Set E)) ∧ LinearIndependent ℝ v}

variable {L : Submodule ℤ E}

variable [FiniteDimensional ℝ E]

section Elementary

variable [DiscreteTopology L] [IsZLattice ℝ L]

/-- Below the dimension there is an admissible dilation: a basis of `E` made of lattice vectors
is independent, and the body absorbs its finitely many members. -/
private theorem exists_mem_minimumSet (hi : i < finrank ℝ E) (hB₀ : Convex ℝ B)
    (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty) :
    ∃ t : ℝ, 0 < t ∧ ∃ v : Fin (i + 1) → E,
      (∀ j, v j ∈ (t • B) ∩ (L : Set E)) ∧ LinearIndependent ℝ v := by
  have h₀ : B ∈ 𝓝 (0 : E) := by
    obtain ⟨x, hx⟩ := hB₂
    have hneg : -x ∈ B := hB₁ x (interior_subset hx)
    have hmem : (0 : E) ∈ interior B := by
      have := hB₀.combo_interior_self_mem_interior hx hneg (a := 1 / 2) (b := 1 / 2)
        (by norm_num) (by norm_num) (by norm_num)
      simpa using this
    exact mem_interior_iff_mem_nhds.1 hmem
  have hstrict {t : ℝ} {x : E} (h : gauge B x < t) : x ∈ t • B := by
    have hx : x ∈ {y : E | gauge B y ≤ gauge B x} := by simp
    rw [setOfPred_gauge_le_eq hB₀ (mem_of_mem_nhds h₀) (absorbent_nhds_zero h₀)
      (gauge_nonneg x)] at hx
    exact mem_iInter₂.1 hx t h
  obtain ⟨b, hb⟩ : ∃ b : Basis (Fin (finrank ℝ E)) ℝ E, ∀ j, b j ∈ L := by
    classical
    have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = finrank ℝ E := by
      rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
    refine ⟨((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).reindex
      (Fintype.equivFinOfCardEq hcard), fun j ↦ ?_⟩
    simp only [Basis.reindex_apply, Basis.ofZLatticeBasis_apply]
    exact SetLike.coe_mem _
  set v : Fin (i + 1) → E := fun j ↦ b (j.castLE hi)
  set t : ℝ := 1 + ∑ j, gauge B (v j)
  have hlt : ∀ j, gauge B (v j) < t := fun j ↦ by
    have : gauge B (v j) ≤ ∑ k, gauge B (v k) :=
      Finset.single_le_sum (fun k _ ↦ gauge_nonneg (v k)) (Finset.mem_univ j)
    linarith
  refine ⟨t, ?_, v, fun j ↦ ⟨hstrict (hlt j), ?_⟩, ?_⟩
  · have : (0 : ℝ) ≤ ∑ j, gauge B (v j) :=
      Finset.sum_nonneg fun j _ ↦ gauge_nonneg (v j)
    linarith
  · exact hb _
  · exact b.linearIndependent.comp _ fun a c h ↦ Fin.castLE_injective hi h

/-- Below the dimension, a lower bound for every admissible dilation is a lower bound for the
minimum. -/
theorem le_successiveMinimum (hi : i < finrank ℝ E) (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B)
    (hB₂ : (interior B).Nonempty) {c : ℝ}
    (H : ∀ t : ℝ, 0 < t → ∀ v : Fin (i + 1) → E, (∀ j, v j ∈ (t • B) ∩ (L : Set E)) →
      LinearIndependent ℝ v → c ≤ t) :
    c ≤ successiveMinimum L B i :=
  le_csInf (exists_mem_minimumSet hi hB₀ hB₁ hB₂) fun _ ht ↦ H _ ht.1 _ ht.2.choose_spec.1
    ht.2.choose_spec.2

end Elementary

/-- The minima are monotone in the index below the dimension: an independent family of `j + 1`
vectors contains one of `i + 1` vectors, so every dilation admissible at `j` is admissible at
`i`. The hypothesis `j < finrank ℝ E` is needed because above the dimension the admissible set
in `successiveMinimum` is empty. -/
theorem successiveMinimum_le_of_le [DiscreteTopology L] [IsZLattice ℝ L] {j : ℕ} (hij : i ≤ j)
    (hj : j < finrank ℝ E) (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B)
    (hB₂ : (interior B).Nonempty) :
    successiveMinimum L B i ≤ successiveMinimum L B j := by
  refine le_csInf (exists_mem_minimumSet hj hB₀ hB₁ hB₂) ?_
  rintro t ⟨ht, v, hv, hind⟩
  have hle : i + 1 ≤ j + 1 := by omega
  refine csInf_le ⟨0, fun _ hs ↦ hs.1.le⟩
    ⟨ht, (fun k ↦ v (k.castLE hle)), (fun k ↦ hv _), ?_⟩
  exact hind.comp _ fun a c h ↦ Fin.castLE_injective hle h

section Discrete

variable [DiscreteTopology L]

/-- A bounded gauge slice meets the lattice in a finite set: the slice is bounded because the body
is, and the lattice is discrete and closed. This is the one place discreteness of the lattice is
used, and every attainment statement below rests on it. -/
private theorem finite_gauge_le_inter (L : Submodule ℤ E) [DiscreteTopology L]
    (h₀ : B ∈ 𝓝 (0 : E)) (hB₃ : Bornology.IsBounded B) (t : ℝ) :
    ({x : E | gauge B x ≤ t} ∩ (L : Set E)).Finite := by
  obtain ⟨R, hR, hRB⟩ := hB₃.subset_closedBall_lt 0 0
  refine Metric.finite_isBounded_inter_isClosed ?_ ?_ ?_
  · exact DiscreteTopology.isDiscrete
  · refine (Metric.isBounded_closedBall (x := (0 : E)) (r := R * t)).subset fun x hx ↦ ?_
    have hx' : ‖x‖ / R ≤ t :=
      le_trans (le_gauge_of_subset_closedBall (absorbent_nhds_zero h₀) hR.le hRB) hx
    rw [mem_closedBall_zero_iff]
    rw [div_le_iff₀ hR] at hx'
    linarith [hx', mul_comm t R]
  · have : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
    rw [← Submodule.coe_toAddSubgroup]
    exact AddSubgroup.isClosed_of_discrete

/-- The gauge attains its minimum on any nonempty set of lattice points: the points of gauge at
most that of a chosen member form a finite set. -/
private theorem exists_gauge_min (L : Submodule ℤ E) [DiscreteTopology L] (h₀ : B ∈ 𝓝 (0 : E))
    (hB₃ : Bornology.IsBounded B) {S : Set E} (hS : S ⊆ (L : Set E)) (hne : S.Nonempty) :
    ∃ w ∈ S, ∀ y ∈ S, gauge B w ≤ gauge B y := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hfin : (S ∩ {x : E | gauge B x ≤ gauge B x₀}).Finite := by
    refine (finite_gauge_le_inter L h₀ hB₃ (gauge B x₀)).subset fun x hx ↦ ⟨hx.2, hS hx.1⟩
  obtain ⟨w, hw, hmin⟩ := Set.exists_min_image _ (gauge B) hfin ⟨x₀, hx₀, by simp⟩
  refine ⟨w, hw.1, fun y hy ↦ ?_⟩
  by_cases hy' : gauge B y ≤ gauge B x₀
  · exact hmin y ⟨hy, hy'⟩
  · exact le_trans (hmin x₀ ⟨hx₀, by simp⟩) (not_le.1 hy').le

variable [IsZLattice ℝ L]

/-- Nonzero lattice points have gauge bounded away from zero. This is where boundedness of the
body is used: the body is inside a ball, so a point of small gauge is a point of small norm, and
the lattice has none but `0`. -/
private theorem exists_pos_le_gauge (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (h₀ : B ∈ 𝓝 (0 : E)) (hB₃ : Bornology.IsBounded B) (hE : 0 < finrank ℝ E) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ (L : Set E), x ≠ 0 → δ ≤ gauge B x := by
  obtain ⟨b, hb⟩ : ∃ b : Basis (Fin (finrank ℝ E)) ℝ E, ∀ j, b j ∈ L := by
    classical
    have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = finrank ℝ E := by
      rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
    refine ⟨((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L).reindex
      (Fintype.equivFinOfCardEq hcard), fun j ↦ ?_⟩
    simp only [Basis.reindex_apply, Basis.ofZLatticeBasis_apply]
    exact SetLike.coe_mem _
  have hne : {x : E | x ∈ (L : Set E) ∧ x ≠ 0}.Nonempty :=
    ⟨b ⟨0, hE⟩, hb _, b.ne_zero _⟩
  obtain ⟨w, hw, hwmin⟩ := exists_gauge_min L h₀ hB₃ (fun y hy ↦ hy.1) hne
  refine ⟨gauge B w, ?_, fun x hx hx0 ↦ hwmin x ⟨hx, hx0⟩⟩
  rw [gauge_pos (absorbent_nhds_zero h₀) ((NormedSpace.isVonNBounded_iff ℝ).2 hB₃)]
  exact hw.2

/-- **The minima are positive.** A nonzero lattice point has gauge bounded away from zero, so no
small dilation of a bounded body can contain one. -/
theorem successiveMinimum_pos (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty)
    (hB₃ : Bornology.IsBounded B) (hi : i < finrank ℝ E) : 0 < successiveMinimum L B i := by
  have h₀ : B ∈ 𝓝 (0 : E) := by
    obtain ⟨x, hx⟩ := hB₂
    have hneg : -x ∈ B := hB₁ x (interior_subset hx)
    have hmem : (0 : E) ∈ interior B := by
      have := hB₀.combo_interior_self_mem_interior hx hneg (a := 1 / 2) (b := 1 / 2)
        (by norm_num) (by norm_num) (by norm_num)
      simpa using this
    exact mem_interior_iff_mem_nhds.1 hmem
  obtain ⟨δ, hδ, hlow⟩ := exists_pos_le_gauge L h₀ hB₃ (by omega)
  refine lt_of_lt_of_le hδ (le_successiveMinimum hi hB₀ hB₁ hB₂ fun t ht v hv hind ↦ ?_)
  exact (hlow (v 0) (hv 0).2 (hind.ne_zero 0)).trans (gauge_le_of_mem ht.le (hv 0).1)

end Discrete

section Attainment

variable [DiscreteTopology L] [IsZLattice ℝ L]

/-- The inductive step of Cassels' Lemma 1, carrying the minimality of the family over the
complement of its own span: that clause is what makes the gauges increase along the family, and
it is the reason the construction is greedy rather than a choice for each index separately. -/
private theorem exists_gauge_eq_aux (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty)
    (hB₃ : Bornology.IsBounded B) :
    ∀ m : ℕ, m ≤ finrank ℝ E → ∃ v : Fin m → E, (∀ j, v j ∈ (L : Set E)) ∧
      LinearIndependent ℝ v ∧ (∀ j : Fin m, gauge B (v j) = successiveMinimum L B j) ∧
      ∀ y ∈ (L : Set E), y ∉ Submodule.span ℝ (Set.range v) → ∀ j, gauge B (v j) ≤ gauge B y := by
  have h₀ : B ∈ 𝓝 (0 : E) := by
    obtain ⟨x, hx⟩ := hB₂
    have hneg : -x ∈ B := hB₁ x (interior_subset hx)
    have hmem : (0 : E) ∈ interior B := by
      have := hB₀.combo_interior_self_mem_interior hx hneg (a := 1 / 2) (b := 1 / 2)
        (by norm_num) (by norm_num) (by norm_num)
      simpa using this
    exact mem_interior_iff_mem_nhds.1 hmem
  have hstrict {t : ℝ} {x : E} (h : gauge B x < t) : x ∈ t • B := by
    have hx : x ∈ {y : E | gauge B y ≤ gauge B x} := by simp
    rw [setOfPred_gauge_le_eq hB₀ (mem_of_mem_nhds h₀) (absorbent_nhds_zero h₀)
      (gauge_nonneg x)] at hx
    exact mem_iInter₂.1 hx t h
  intro m
  induction m with
  | zero =>
    exact fun _ ↦ ⟨Fin.elim0, fun j ↦ j.elim0, linearIndependent_empty_type, fun j ↦ j.elim0,
      fun _ _ _ j ↦ j.elim0⟩
  | succ m ih =>
    intro hm
    obtain ⟨v, hvL, hvind, hvmin, hvlow⟩ := ih (by omega)
    have hrank : finrank ℝ (Submodule.span ℝ (Set.range v)) = m := by
      rw [finrank_span_eq_card hvind, Fintype.card_fin]
    have hWlt : Submodule.span ℝ (Set.range v) < ⊤ :=
      Submodule.lt_top_of_finrank_lt_finrank (by rw [hrank]; omega)
    have hne : {y : E | y ∈ (L : Set E) ∧ y ∉ Submodule.span ℝ (Set.range v)}.Nonempty := by
      by_contra hcon
      rw [not_nonempty_iff_eq_empty, eq_empty_iff_forall_notMem] at hcon
      refine hWlt.ne (top_le_iff.1 ?_)
      rw [← (IsZLattice.span_top (K := ℝ) (L := L) : Submodule.span ℝ (L : Set E) = ⊤)]
      refine Submodule.span_le.2 fun y hy ↦ ?_
      by_contra hyW
      exact hcon y ⟨hy, hyW⟩
    obtain ⟨w, hw, hwmin⟩ := exists_gauge_min L h₀ hB₃ (fun y hy ↦ hy.1) hne
    obtain ⟨hwL, hwW⟩ := hw
    have hgle : ∀ j : Fin (m + 1), gauge B ((Fin.snoc v w : Fin (m + 1) → E) j) ≤ gauge B w := by
      refine Fin.lastCases ?_ fun k ↦ ?_
      · simp
      · simpa using hvlow w hwL hwW k
    have hv'ind : LinearIndependent ℝ (Fin.snoc v w : Fin (m + 1) → E) := hvind.finSnoc hwW
    have hv'L : ∀ j : Fin (m + 1), (Fin.snoc v w : Fin (m + 1) → E) j ∈ (L : Set E) := by
      refine Fin.lastCases ?_ fun k ↦ ?_
      · simpa using hwL
      · simpa using hvL k
    have hgw : gauge B w = successiveMinimum L B m := by
      refine le_antisymm ?_ ?_
      · refine le_successiveMinimum (by omega) hB₀ hB₁ hB₂ fun t ht u hu huind ↦ ?_
        have hex : ∃ k, u k ∉ Submodule.span ℝ (Set.range v) := by
          by_contra hcon
          rw [not_exists] at hcon
          have hle : Submodule.span ℝ (Set.range u) ≤ Submodule.span ℝ (Set.range v) := by
            refine Submodule.span_le.2 ?_
            rintro _ ⟨k, rfl⟩
            exact not_not.1 (hcon k)
          have := Submodule.finrank_mono hle
          rw [finrank_span_eq_card huind, Fintype.card_fin, hrank] at this
          omega
        obtain ⟨k, hk⟩ := hex
        exact (hwmin (u k) ⟨(hu k).2, hk⟩).trans (gauge_le_of_mem ht.le (hu k).1)
      · refine le_of_forall_gt_imp_ge_of_dense fun t ht ↦ ?_
        refine csInf_le ⟨0, fun _ hs ↦ hs.1.le⟩
          ⟨lt_of_le_of_lt (gauge_nonneg w) ht, Fin.snoc v w,
            (fun j ↦ ⟨?_, hv'L j⟩), hv'ind⟩
        exact hstrict (lt_of_le_of_lt (hgle j) ht)
    refine ⟨Fin.snoc v w, hv'L, hv'ind, ?_, ?_⟩
    · refine Fin.lastCases ?_ fun k ↦ ?_
      · simpa using hgw
      · simpa using hvmin k
    · intro y hy hyW
      have hsub : Set.range v ⊆ Set.range (Fin.snoc v w : Fin (m + 1) → E) := by
        rw [Set.range_subset_iff]
        exact fun k ↦ ⟨k.castSucc, by simp⟩
      have hyW' : y ∉ Submodule.span ℝ (Set.range v) := fun h ↦
        hyW (Submodule.span_mono hsub h)
      refine Fin.lastCases ?_ fun k ↦ ?_
      · simpa using hwmin y ⟨hy, hyW'⟩
      · simpa using hvlow y hy hyW' k

/-- **Cassels' Lemma 1: the successive minima are attained.** There is a single family of
`finrank ℝ E` linearly independent lattice vectors whose gauges are the successive minima — not
one family for each index. This is the statement every later proof consumes.

⚠ No closedness of the body is needed here; see
`exists_linearIndependent_mem_smul_successiveMinimum` for the body form, which does need it. -/
theorem exists_linearIndependent_gauge_eq_successiveMinimum (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B)
    (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B) :
    ∃ v : Fin (finrank ℝ E) → E, (∀ j, v j ∈ (L : Set E)) ∧ LinearIndependent ℝ v ∧
      ∀ j : Fin (finrank ℝ E), gauge B (v j) = successiveMinimum L B j :=
  let ⟨v, hvL, hvind, hvmin, _⟩ := exists_gauge_eq_aux L hB₀ hB₁ hB₂ hB₃ (finrank ℝ E) le_rfl
  ⟨v, hvL, hvind, hvmin⟩

/-- The body form of Cassels' Lemma 1: the independent lattice vectors realizing the minima lie in
the corresponding dilations of the body. This is the form Minkowski's second theorem and the basis
lemma of Layer 4.6 consume, and `IsClosed B` is exactly what it costs over the gauge form. -/
theorem exists_linearIndependent_mem_smul_successiveMinimum (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B)
    (hB₂ : (interior B).Nonempty) (hB₃ : Bornology.IsBounded B) (hB₄ : IsClosed B) :
    ∃ v : Fin (finrank ℝ E) → E, (∀ j, v j ∈ (L : Set E)) ∧ LinearIndependent ℝ v ∧
      ∀ j : Fin (finrank ℝ E), v j ∈ (successiveMinimum L B j) • B := by
  have h₀ : B ∈ 𝓝 (0 : E) := by
    obtain ⟨x, hx⟩ := hB₂
    have hneg : -x ∈ B := hB₁ x (interior_subset hx)
    have hmem : (0 : E) ∈ interior B := by
      have := hB₀.combo_interior_self_mem_interior hx hneg (a := 1 / 2) (b := 1 / 2)
        (by norm_num) (by norm_num) (by norm_num)
      simpa using this
    exact mem_interior_iff_mem_nhds.1 hmem
  have hweak {t : ℝ} (ht : 0 < t) {x : E} : gauge B x ≤ t ↔ x ∈ t • B := by
    refine ⟨fun h ↦ ?_, gauge_le_of_mem ht.le⟩
    have h1 : gauge B (t⁻¹ • x) ≤ 1 := by
      rw [gauge_smul_of_nonneg (inv_nonneg.2 ht.le), smul_eq_mul, inv_mul_le_iff₀ ht, mul_one]
      exact h
    have h2 : t⁻¹ • x ∈ B := by
      rw [← hB₄.closure_eq]
      exact (gauge_le_one_iff_mem_closure hB₀ h₀).1 h1
    rwa [mem_smul_set_iff_inv_smul_mem₀ ht.ne']
  obtain ⟨v, hvL, hvind, hvg⟩ :=
    exists_linearIndependent_gauge_eq_successiveMinimum L hB₀ hB₁ hB₂ hB₃
  refine ⟨v, hvL, hvind, fun j ↦ ?_⟩
  have hpos : 0 < successiveMinimum L B j :=
    successiveMinimum_pos L hB₀ hB₁ hB₂ hB₃ j.isLt
  rw [← hweak hpos, hvg j]

/-- **The dependence half of Cassels' Lemma 1.** Outside the span of the first `j` members of a
family realizing the minima there is nothing of gauge below the `j`-th minimum. The point would
extend those `j` members to an independent family of `j + 1` lattice points, which bounds the
`j`-th minimum by the largest gauge in the family; the induction on `j` is what identifies that
largest gauge as the gauge of the new point, since without it the bound is only by the maximum of
the new gauge and the `(j - 1)`-st minimum, and those can be equal. -/
theorem successiveMinimum_le_gauge_of_notMem_span (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : (interior B).Nonempty)
    {v : Fin (finrank ℝ E) → E} (hvL : ∀ i, v i ∈ (L : Set E)) (hvind : LinearIndependent ℝ v)
    (hvg : ∀ i, gauge B (v i) = successiveMinimum L B i) :
    ∀ j : ℕ, j ≤ finrank ℝ E → ∀ y ∈ (L : Set E),
      y ∉ Submodule.span ℝ (v '' {i : Fin (finrank ℝ E) | (i : ℕ) < j}) →
        successiveMinimum L B j ≤ gauge B y := by
  have h₀ : B ∈ 𝓝 (0 : E) := by
    obtain ⟨x, hx⟩ := hB₂
    have hneg : -x ∈ B := hB₁ x (interior_subset hx)
    have hmem : (0 : E) ∈ interior B := by
      have := hB₀.combo_interior_self_mem_interior hx hneg (a := 1 / 2) (b := 1 / 2)
        (by norm_num) (by norm_num) (by norm_num)
      simpa using this
    exact mem_interior_iff_mem_nhds.1 hmem
  have hstrict {t : ℝ} {x : E} (h : gauge B x < t) : x ∈ t • B := by
    have hx : x ∈ {y : E | gauge B y ≤ gauge B x} := by simp
    rw [setOfPred_gauge_le_eq hB₀ (mem_of_mem_nhds h₀) (absorbent_nhds_zero h₀)
      (gauge_nonneg x)] at hx
    exact mem_iInter₂.1 hx t h
  intro j
  induction j with
  | zero =>
    intro _ y hy hspan
    refine le_of_forall_gt_imp_ge_of_dense fun t ht ↦ ?_
    have htpos : 0 < t := lt_of_le_of_lt (gauge_nonneg _) ht
    have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    refine csInf_le ⟨0, fun _ hs ↦ hs.1.le⟩
      ⟨htpos, (fun _ : Fin (0 + 1) ↦ y),
        (fun _ ↦ ⟨hstrict ht, hy⟩), ?_⟩
    refine (linearIndependent_subsingleton_index_iff _).2 fun _ ↦ ?_
    intro hy0
    rw [hy0] at hspan
    exact hspan (Submodule.zero_mem _)
  | succ j ih =>
    intro hj y hy hspan
    have hjn : j < finrank ℝ E := hj
    have hprev : successiveMinimum L B j ≤ gauge B y :=
      ih hjn.le y hy fun h ↦
        hspan (Submodule.span_mono (Set.image_mono fun i hi ↦ Nat.lt_succ_of_lt hi) h)
    have hrange : Set.range (v ∘ Fin.castLE hj)
        = v '' {i : Fin (finrank ℝ E) | (i : ℕ) < j + 1} := by
      rw [Set.range_comp, Fin.range_castLE]
    refine le_of_forall_gt_imp_ge_of_dense fun t ht ↦ ?_
    have htpos : 0 < t := lt_of_le_of_lt (gauge_nonneg _) ht
    refine csInf_le ⟨0, fun _ hs ↦ hs.1.le⟩
      ⟨htpos, Fin.snoc (v ∘ Fin.castLE hj) y, ?_, ?_⟩
    · refine Fin.lastCases ?_ (fun k ↦ ?_)
      · rw [Fin.snoc_last]
        exact ⟨hstrict ht, hy⟩
      · rw [Fin.snoc_castSucc]
        refine ⟨hstrict ?_, hvL _⟩
        calc gauge B ((v ∘ Fin.castLE hj) k) = successiveMinimum L B (k.castLE hj) := hvg _
          _ ≤ successiveMinimum L B j :=
              successiveMinimum_le_of_le (by simpa using Fin.is_le k) hjn hB₀ hB₁ hB₂
          _ ≤ gauge B y := hprev
          _ < t := ht
    · rw [linearIndependent_finSnoc]
      exact ⟨hvind.comp _ fun _ _ h ↦ Fin.castLE_injective hj h, fun hmem ↦ hspan (hrange ▸ hmem)⟩

end Attainment

end ZLattice

section Regrouping

/-- **Every `d`-th term, to the power `d`, against the whole product.** For a nonnegative sequence
that is monotone below `N`, the product of `f (d * j) ^ d` over `j < k` is at most the product of
`f i` over `i < d * k`. This is what turns Minkowski's second theorem — a bound on the product of
all `d * k` successive minima — into a bound on a product of `k` heights, each of which costs a
`d`-th power. -/
theorem Finset.prod_pow_le_prod_range {f : ℕ → ℝ} {N : ℕ} (hf0 : ∀ i, 0 ≤ f i)
    (hmono : ∀ i j, i ≤ j → j < N → f i ≤ f j) (d : ℕ) :
    ∀ k, d * k ≤ N → ∏ j ∈ Finset.range k, f (d * j) ^ d ≤ ∏ i ∈ Finset.range (d * k), f i := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hle
    have hk : d * k ≤ N := le_trans (Nat.mul_le_mul_left d (Nat.le_succ k)) hle
    have hsplit : d * (k + 1) = d * k + d := by ring
    rw [Finset.prod_range_succ, hsplit, Finset.prod_range_add]
    refine mul_le_mul (ih hk) ?_ (pow_nonneg (hf0 _) _)
      (Finset.prod_nonneg fun i _ ↦ hf0 i)
    calc f (d * k) ^ d = ∏ _i ∈ Finset.range d, f (d * k) := by
          rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ i ∈ Finset.range d, f (d * k + i) := by
          refine Finset.prod_le_prod (fun i _ ↦ hf0 _) fun i hi ↦ ?_
          rw [Finset.mem_range] at hi
          exact hmono _ _ (Nat.le_add_right _ _) (by omega)

end Regrouping

section Examples

open ZLattice

variable [FiniteDimensional ℝ E] {L : Submodule ℤ E}

end Examples
