/- GID: D5/S3/Combinatorics/Geometry/MiuraEqualitySides
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraEqualitySides
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: Actual two-type equality excludes neutral profiles before the opposite boundary slab. -/
module
public import D5.S3.Combinatorics.Geometry.MiuraEqualityCrossed
import all D5.S3.Combinatorics.Geometry.MiuraEqualityNeutral
import all D5.S3.Combinatorics.Geometry.MiuraEqualityCrossed
import all D5.S3.Combinatorics.Geometry.MiuraEqualitySaturation
import all D5.S3.Combinatorics.Geometry.MiuraEqualityProfile
import all D5.S3.Combinatorics.Geometry.MiuraSlabIncidence
import all D5.S3.Combinatorics.Geometry.MiuraSlabBudget
import all D5.S3.Combinatorics.Geometry.MiuraSlabSigns

/-! Neutral-column profiles and actual boundary-slab rigidity. -/
@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraEqualitySides
open MiuraHeightEnvelope MiuraStripRigidity MiuraSlabExtrema MiuraSlabNeutral
open MiuraSlabIncidence MiuraSlabBudget MiuraSlabRunBound MiuraSlabCover MiuraSlabClassification
open MiuraSlabSigns
open MiuraEqualityNeutral MiuraEqualityCrossed MiuraEqualitySaturation MiuraEqualityProfile
variable {m n : ℕ}

private theorem prefix_without_maximum {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 0 < m) (i : Fin m)
    (hno : ∀ v : Cell m n, v.1.val < i.val → ¬ IsStrictLocalMax h v)
    (j : Fin n) : h (i, j) = h (⟨0, hm⟩, j) + (i.val : ℤ) := by
  have he := prefix_without_minimum (neg_height hh) hm i (by
    intro v hv hx
    exact hno v hv ((neg_min_iff h v).mp hx)) j
  omega

private theorem top_profile_min_ambient {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hno : ∀ j : Fin n, ¬ IsStrictLocalMax h (⟨0, by omega⟩, j))
    (j : Fin n) (hj : IsStrictLocalMin (profile h ⟨0, by omega⟩) (0, j)) :
    IsStrictLocalMin h (⟨0, by omega⟩, j) := by
  have hp : IsStrictLocalMax (profile (fun v => -h v) ⟨0, by omega⟩) (0, j) :=
    (neg_max_iff (profile h ⟨0, by omega⟩) (0, j)).mpr hj
  have he := top_profile_max_ambient (neg_height hh) hm
    (fun j hx => hno j ((neg_min_iff h _).mp hx)) j hp
  exact (neg_max_iff h _).mp he

private theorem top_minimum_profile_no_neutral_peak {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hr : ∃ i, ¬ RowOccupied h i) (hc : ∃ j, ¬ RowOccupied (transposeHeight h) j)
    (heq : (extrema h).card = (frozenRowRunStarts h).card +
      (frozenRowRunStarts (transposeHeight h)).card)
    (I : Interval m) (hI : I ∈ minRowSlabs h) (hi : I.Contains ⟨0, by omega⟩)
    (J : Interval n) (hJ : J ∈ neutralColSlabs h) (j : Fin n) (hjJ : J.Contains j) :
    ¬ IsStrictLocalMax (profile h ⟨0, by omega⟩) (0, j) := by
  classical
  intro hp
  have he := run_equality_charge hh hm hn hr hc heq
  have hno := (equality_slab_extrema_sign hh hm (by omega) he).1 I hI
  let f := transposeHeight (profile h (⟨0, by omega⟩ : Fin m))
  have hf : IsHeight f := transpose_isHeight (profile_isHeight hh _)
  obtain ⟨_, s, hs, ht, hb, hct, hcb⟩ := Finset.mem_filter.mp hJ
  have hcuts : EqualRowCuts f J s := by
    refine ⟨ht, hb, ?_, ?_⟩ <;> intro k
    · exact hct ⟨0, by omega⟩
    · exact hcb ⟨0, by omega⟩
  have hp' : IsStrictLocalMax f (j, 0) := by
    intro u hu
    apply hp (u.2, u.1)
    simp only [adj, gdist] at hu ⊢
    omega
  obtain ⟨⟨u, huJ, humin⟩, _⟩ := neutral_row_has_both hf J s hs hcuts
    ⟨j, hjJ, 0, Or.inr hp'⟩
  have hprofmin : IsStrictLocalMin (profile h ⟨0, by omega⟩) (0, u.1) := by
    have hmin := transpose_min humin
    have hu0 : u.2 = (0 : Fin 1) := Subsingleton.elim _ _
    simpa only [hu0] using hmin
  have hmin := top_profile_min_ambient hh hm (fun j => hno _ hi) u.1 hprofmin
  have hsup : ((⟨0, by omega⟩, u.1) : Cell m n) ∈ colNeutralSupport h := by
    apply Finset.mem_biUnion.mpr
    refine ⟨J, hJ, ?_⟩
    simp only [colIncidences, extrema, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Or.inl hmin, huJ⟩
  have hsupp := (frozen_run_equality_incidence hh hm hn hr hc heq).1
  have hin := row_neutral_interior (hsupp.symm ▸ hsup)
  change 0 < 0 ∧ _ at hin
  omega

/-- At actual run equality, a top minimum slab and a unique bottom maximum
slab exclude all neutral slabs. The first maximum is derived from the same
array and its top profile, rather than supplied as an incidence witness. -/
theorem equality_no_neutral_top_minimum {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hr : ∃ i, ¬ RowOccupied h i) (hc : ∃ j, ¬ RowOccupied (transposeHeight h) j)
    (heq : (extrema h).card = (frozenRowRunStarts h).card +
      (frozenRowRunStarts (transposeHeight h)).card)
    (hmax : (maxRowSlabs h).card = 1)
    (I J : Interval m) (hI : I ∈ minRowSlabs h) (hJ : J ∈ maxRowSlabs h)
    (ht : I.Contains ⟨0, by omega⟩) (hb : J.Contains ⟨m - 1, by omega⟩) :
    neutralRowSlabs h = ∅ ∧ neutralColSlabs h = ∅ := by
  classical
  let S := MiuraResidualCount.maxima h
  have hS : S.Nonempty := by
    obtain ⟨⟨v, hv, _⟩, _⟩ := envelope_max hh ((⟨0, by omega⟩, ⟨0, by omega⟩) : Cell m n)
    exact ⟨v, by simp [S, MiuraResidualCount.maxima, hv]⟩
  obtain ⟨v, hvS, hvleast⟩ := Finset.exists_min_image S (fun v => v.1.val) hS
  have hv : IsStrictLocalMax h v := by simpa [S, MiuraResidualCount.maxima] using hvS
  have hfirst (u : Cell m n) (hu : u.1.val < v.1.val) : ¬ IsStrictLocalMax h u := by
    intro hmaxu
    have huS : u ∈ S := by simp [S, MiuraResidualCount.maxima, hmaxu]
    have := hvleast u huS
    omega
  have hshift (j : Fin n) : h (v.1, j) = h (⟨0, by omega⟩, j) + (v.1.val : ℤ) :=
    prefix_without_maximum hh (by omega) v.1 hfirst j
  have hprof : IsStrictLocalMax (profile h v.1) (0, v.2) := by
    intro u hu
    apply hv (v.1, u.2)
    simp only [adj, gdist] at hu ⊢
    omega
  have htoppeak := (profile_max_of_shift v.1 (⟨0, by omega⟩ : Fin m) (v.1.val : ℤ) hshift v.2).mp hprof
  have hnc : v ∉ colNeutralSupport h := by
    intro hnc
    obtain ⟨K, hK, hvK⟩ := Finset.mem_biUnion.mp hnc
    exact top_minimum_profile_no_neutral_peak hh hm hn hr hc heq I hI ht K hK v.2
      (Finset.mem_filter.mp hvK).2 htoppeak
  have hsupp := (frozen_run_equality_incidence hh hm hn hr hc heq).1
  have hnr : v ∉ rowNeutralSupport h := fun hvn => hnc (hsupp ▸ hvn)
  have hnot : v ∉ neutralSupport h := by
    simp only [neutralSupport, Finset.mem_union, not_or]
    exact ⟨hnr, hnc⟩
  have hev : v ∈ extrema h := by simp [extrema, hv]
  have he := run_equality_charge hh hm hn hr hc heq
  have hvJ : J.Contains v.1 := by
    rcases equality_nonneutral_extremum hh hm (by omega) he v hev hnot with
      ⟨K, hK, L, hL, hvK, hvL, hmin⟩ | ⟨K, hK, L, hL, hvK, _⟩
    · exact (minimum_maximum_distinct hm h v v hmin hv rfl).elim
    · have hKJ : K = J := Finset.card_le_one_iff.mp (by omega : (maxRowSlabs h).card ≤ 1) hK hJ
      exact hKJ ▸ hvK
  have hr0 : neutralRowSlabs h = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro K hK
    obtain ⟨hKs, s, hs, hcuts⟩ := Finset.mem_filter.mp hK
    have hKs' : IsRowSlab h K := (Finset.mem_filter.mp hKs).2
    obtain ⟨_, w, hwK, hwmax⟩ := neutral_row_has_both hh K s hs hcuts
      ⟨K.first, ⟨le_rfl, K.ordered⟩, hKs'.1 K.first ⟨le_rfl, K.ordered⟩⟩
    have hwS : w ∈ S := by simp [S, MiuraResidualCount.maxima, hwmax]
    have hvw := hvleast w hwS
    have hwJ : J.Contains w.1 := by
      change J.first.val ≤ w.1.val ∧ w.1.val ≤ J.last.val
      change J.first.val ≤ v.1.val ∧ v.1.val ≤ J.last.val at hvJ
      change J.first.val ≤ m - 1 ∧ m - 1 ≤ J.last.val at hb
      have := w.1.isLt
      omega
    have hKJ : K = J := row_slab_unique hKs'
      (Finset.mem_filter.mp (Finset.mem_filter.mp hJ).1).2 w.1 hwK hwJ
    subst K
    exact neutral_not_outward (by omega) J s (-1) (by norm_num) hcuts (Finset.mem_filter.mp hJ).2.2
  have hcounts := (frozen_run_equality_incidence hh hm hn hr hc heq).2.1
  have hc0 : neutralColSlabs h = ∅ := Finset.card_eq_zero.mp (by rw [hr0] at hcounts; simpa using hcounts.symm)
  exact ⟨hr0, hc0⟩
private theorem neutral_mem_neg {h : Cell m n → ℤ} (K : Interval m)
    (hK : K ∈ neutralRowSlabs h) : K ∈ neutralRowSlabs (fun v => -h v) := by
  classical
  obtain ⟨hKs, s, hs, ht, hb, hct, hcb⟩ := Finset.mem_filter.mp hK
  have hKs' : IsRowSlab h K := (Finset.mem_filter.mp hKs).2
  have hKn : IsRowSlab (fun v => -h v) K := by simpa only [IsRowSlab, neg_occupied] using hKs'
  simp only [neutralRowSlabs, rowSlabs, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hKn, -s, ?_, ht, hb, ?_, ?_⟩
  · rcases hs with rfl | rfl <;> norm_num
  · intro j; have he := hct j; change -h (K.first, j) = -h (⟨K.first.val - 1, _⟩, j) + -s; omega
  · intro j; have he := hcb j; change -h (⟨K.last.val + 1, _⟩, j) = -h (K.last, j) + -s; omega

/-- An actual equality array with one minimum row slab and one maximum row
slab has no neutral slabs, including both boundary orientations. -/
theorem equality_two_row_types_no_neutral {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hr : ∃ i, ¬ RowOccupied h i) (hc : ∃ j, ¬ RowOccupied (transposeHeight h) j)
    (heq : (extrema h).card = (frozenRowRunStarts h).card +
      (frozenRowRunStarts (transposeHeight h)).card)
    (hmin : (minRowSlabs h).card = 1) (hmax : (maxRowSlabs h).card = 1) :
    neutralRowSlabs h = ∅ ∧ neutralColSlabs h = ∅ := by
  classical
  obtain ⟨I, ht, hIs⟩ := occupied_row_has_slab h ⟨0, by omega⟩ (MiuraSlabFrozen.boundary_rows_occupied hh hm (by omega)).1
  obtain ⟨J, hb, hJs⟩ := occupied_row_has_slab h ⟨m - 1, by omega⟩ (MiuraSlabFrozen.boundary_rows_occupied hh hm (by omega)).2
  have hne : I ≠ J := by
    intro he; subst J
    obtain ⟨i, hi⟩ := hr
    apply hi (hIs.1 i ?_)
    change I.first.val ≤ i.val ∧ i.val ≤ I.last.val
    change I.first.val ≤ 0 ∧ 0 ≤ I.last.val at ht
    change I.first.val ≤ m - 1 ∧ m - 1 ≤ I.last.val at hb
    have := i.isLt
    omega
  have hJnon : J ∈ minRowSlabs h ∨ J ∈ maxRowSlabs h := by
    rcases row_slab_classification hh hm (by omega) hr J hJs with hj | hj | hj
    · exact Or.inl hj
    · exact Or.inr hj
    · obtain ⟨_, s, hs, hj0, hj1, _⟩ := Finset.mem_filter.mp hj
      change J.first.val ≤ m - 1 ∧ m - 1 ≤ J.last.val at hb
      omega
  rcases row_slab_classification hh hm (by omega) hr I hIs with hI | hI | hI
  · have hJ : J ∈ maxRowSlabs h := by
      rcases hJnon with hj | hj
      · exact (hne (Finset.card_le_one_iff.mp (by omega : (minRowSlabs h).card ≤ 1) hI hj)).elim
      · exact hj
    exact equality_no_neutral_top_minimum hh hm hn hr hc heq hmax I J hI hJ ht hb
  · have hJ : J ∈ minRowSlabs h := by
      rcases hJnon with hj | hj
      · exact hj
      · exact (hne (Finset.card_le_one_iff.mp (by omega : (maxRowSlabs h).card ≤ 1) hI hj)).elim
    let g : Cell m n → ℤ := fun v => -h v
    have hrg : ∃ i, ¬ RowOccupied g i := by
      obtain ⟨i, hi⟩ := hr
      exact ⟨i, fun h => hi ((neg_occupied _ i).mp h)⟩
    have hcg : ∃ j, ¬ RowOccupied (transposeHeight g) j := by
      obtain ⟨j, hj⟩ := hc
      exact ⟨j, fun h => hj ((neg_occupied _ j).mp h)⟩
    have he : (extrema g).card = (frozenRowRunStarts g).card +
        (frozenRowRunStarts (transposeHeight g)).card := by
      change (extrema (fun u => -h u)).card =
        (frozenRowRunStarts (fun u => -h u)).card +
        (frozenRowRunStarts (fun u => -(transposeHeight h) u)).card
      rw [neg_extrema, neg_runs, neg_runs]
      exact heq
    have hIg : I ∈ minRowSlabs g := by rw [show minRowSlabs g = maxRowSlabs h from neg_min_slabs h]; exact hI
    have hJg : J ∈ maxRowSlabs g := by rw [show maxRowSlabs g = minRowSlabs h from neg_max_slabs h]; exact hJ
    have hmaxg : (maxRowSlabs g).card = 1 := by rw [show maxRowSlabs g = minRowSlabs h from neg_max_slabs h]; exact hmin
    have hr0g := (equality_no_neutral_top_minimum (neg_height hh) hm hn hrg hcg he hmaxg I J hIg hJg ht hb).1
    have hr0 : neutralRowSlabs h = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro K hK
      have hKg := neutral_mem_neg K hK
      rw [hr0g] at hKg
      exact Finset.notMem_empty K hKg
    have hc0 : neutralColSlabs h = ∅ := Finset.card_eq_zero.mp (by
      have hcounts := (frozen_run_equality_incidence hh hm hn hr hc heq).2.1
      rw [hr0] at hcounts
      simpa using hcounts.symm)
    exact ⟨hr0, hc0⟩
  · obtain ⟨_, s, hs, hi0, _⟩ := Finset.mem_filter.mp hI
    change I.first.val ≤ 0 ∧ 0 ≤ I.last.val at ht
    omega

private theorem suffix_without_maximum {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 0 < m) (i : Fin m)
    (hno : ∀ v : Cell m n, i.val < v.1.val → ¬ IsStrictLocalMax h v)
    (j : Fin n) : h (i, j) = h (⟨m - 1, by omega⟩, j) + ((m - 1 - i.val : ℕ) : ℤ) := by
  have he := suffix_without_minimum (neg_height hh) hm i (by
    intro v hv hx
    exact hno v hv ((neg_min_iff h v).mp hx)) j
  omega

private theorem minimum_in_top_slab {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (I : Interval m) (ht : I.Contains ⟨0, by omega⟩)
    (hno : ∀ v : Cell m n, I.Contains v.1 → ¬ IsStrictLocalMax h v)
    (v : Cell m n) (hvI : I.Contains v.1) (hv : IsStrictLocalMin h v) : v.1.val = 0 := by
  by_contra hv0
  have hno' (u : Cell m n) (hu : u.1.val < v.1.val) : ¬ IsStrictLocalMax h u := by
    apply hno u
    change I.first.val ≤ u.1.val ∧ u.1.val ≤ I.last.val
    change I.first.val ≤ 0 ∧ 0 ≤ I.last.val at ht
    change I.first.val ≤ v.1.val ∧ v.1.val ≤ I.last.val at hvI
    omega
  let p : Fin m := ⟨v.1.val - 1, by have := v.1.isLt; omega⟩
  have hve := prefix_without_maximum hh (by omega) v.1 hno' v.2
  have hpe := prefix_without_maximum hh (by omega) p (by
    intro u hu; apply hno' u; dsimp [p] at hu; omega) v.2
  have hmin := hv (p, v.2) (by simp only [adj, gdist, p]; omega)
  change h (p, v.2) = h (v.1, v.2) + 1 at hmin
  dsimp [p] at hpe hmin
  omega

private theorem minimum_in_bottom_slab {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (I : Interval m) (hb : I.Contains ⟨m - 1, by omega⟩)
    (hno : ∀ v : Cell m n, I.Contains v.1 → ¬ IsStrictLocalMax h v)
    (v : Cell m n) (hvI : I.Contains v.1) (hv : IsStrictLocalMin h v) : v.1.val + 1 = m := by
  by_contra hv1
  have hno' (u : Cell m n) (hu : v.1.val < u.1.val) : ¬ IsStrictLocalMax h u := by
    apply hno u
    change I.first.val ≤ u.1.val ∧ u.1.val ≤ I.last.val
    change I.first.val ≤ m - 1 ∧ m - 1 ≤ I.last.val at hb
    change I.first.val ≤ v.1.val ∧ v.1.val ≤ I.last.val at hvI
    have := u.1.isLt
    omega
  let p : Fin m := ⟨v.1.val + 1, by have := v.1.isLt; omega⟩
  have hve := suffix_without_maximum hh (by omega) v.1 hno' v.2
  have hpe := suffix_without_maximum hh (by omega) p (by
    intro u hu; apply hno' u; dsimp [p] at hu; omega) v.2
  have hmin := hv (p, v.2) (by simp only [adj, gdist, p]; omega)
  change h (p, v.2) = h (v.1, v.2) + 1 at hmin
  dsimp [p] at hpe hmin
  have := v.1.isLt
  omega

/-- With one actual minimum row slab and one maximum row slab, equality puts
all minima on one common physical top or bottom side. -/
theorem equality_two_row_types_minima_boundary {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hr : ∃ i, ¬ RowOccupied h i) (hc : ∃ j, ¬ RowOccupied (transposeHeight h) j)
    (heq : (extrema h).card = (frozenRowRunStarts h).card +
      (frozenRowRunStarts (transposeHeight h)).card)
    (hmin : (minRowSlabs h).card = 1) (hmax : (maxRowSlabs h).card = 1) :
    (∀ v : Cell m n, IsStrictLocalMin h v → v.1.val = 0) ∨
    (∀ v : Cell m n, IsStrictLocalMin h v → v.1.val + 1 = m) := by
  classical
  obtain ⟨hr0, hc0⟩ := equality_two_row_types_no_neutral hh hm hn hr hc heq hmin hmax
  have he := run_equality_charge hh hm hn hr hc heq
  obtain ⟨I, hIset⟩ := Finset.card_eq_one.mp hmin
  have hI : I ∈ minRowSlabs h := by rw [hIset]; simp
  have hsign := (equality_slab_extrema_sign hh hm (by omega) he).1 I hI
  have hall (v : Cell m n) (hv : IsStrictLocalMin h v) : I.Contains v.1 := by
    have hev : v ∈ extrema h := by simp [extrema, hv]
    have hnot : v ∉ neutralSupport h := by
      simp only [neutralSupport, rowNeutralSupport, colNeutralSupport, hr0, hc0,
        Finset.biUnion_empty, Finset.union_self, Finset.notMem_empty, not_false_eq_true]
    rcases equality_nonneutral_extremum hh hm (by omega) he v hev hnot with
      ⟨K, hK, L, hL, hvK, _⟩ | ⟨K, hK, L, hL, hvK, hvL, hmaxv⟩
    · have hKI : K = I := Finset.mem_singleton.mp (hIset ▸ hK)
      exact hKI ▸ hvK
    · exact (minimum_maximum_distinct hm h v v hv hmaxv rfl).elim
  have hcard : (rowSlabs h).card = 2 := by
    have hp := row_slab_card_partition hh hm (by omega) hr
    rw [hmin, hmax, hr0] at hp
    simpa using hp
  obtain ⟨T, ht, hTs⟩ := occupied_row_has_slab h ⟨0, by omega⟩ (MiuraSlabFrozen.boundary_rows_occupied hh hm (by omega)).1
  obtain ⟨B, hb, hBs⟩ := occupied_row_has_slab h ⟨m - 1, by omega⟩ (MiuraSlabFrozen.boundary_rows_occupied hh hm (by omega)).2
  have hTB : T ≠ B := by
    intro he; subst B
    obtain ⟨i, hi⟩ := hr
    apply hi (hTs.1 i ?_)
    change T.first.val ≤ i.val ∧ i.val ≤ T.last.val
    change T.first.val ≤ 0 ∧ 0 ≤ T.last.val at ht
    change T.first.val ≤ m - 1 ∧ m - 1 ≤ T.last.val at hb
    have := i.isLt
    omega
  have hset : ({T, B} : Finset (Interval m)) = rowSlabs h := by
    apply Finset.eq_of_subset_of_card_le
    · intro K hK
      rcases Finset.mem_insert.mp hK with rfl | hK
      · simp [rowSlabs, hTs]
      · have he : K = B := Finset.mem_singleton.mp hK
        subst K; simp [rowSlabs, hBs]
    · simp only [hcard, Finset.card_pair hTB]
      omega
  have hItb : I = T ∨ I = B := by
    have hi := (Finset.mem_filter.mp hI).1
    rw [← hset] at hi
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
  rcases hItb with hit | hib
  · have htI : I.Contains ⟨0, by omega⟩ := hit.symm ▸ ht
    exact Or.inl (fun v hv => minimum_in_top_slab hh hm I htI hsign v (hall v hv) hv)
  · have hbI : I.Contains ⟨m - 1, by omega⟩ := hib.symm ▸ hb
    exact Or.inr (fun v hv => minimum_in_bottom_slab hh hm I hbI hsign v (hall v hv) hv)

end D5.S3.Combinatorics.Geometry.MiuraEqualitySides
