/- GID: D5/S3/Combinatorics/Geometry/MiuraEqualityNeutral
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraEqualityNeutral
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: Actual equality excludes neutral incidences on physical boundaries. -/
module
public import D5.S3.Combinatorics.Geometry.MiuraEqualitySaturation
public import D5.S3.Combinatorics.Geometry.MiuraEqualityProfile
import all D5.S3.Combinatorics.Geometry.MiuraSlabRunBound
import all D5.S3.Combinatorics.Geometry.MiuraEqualityProfile

/-! Physical boundary and profile constraints on actual equality arrays. -/
@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraEqualityNeutral
open MiuraHeightEnvelope MiuraStripRigidity MiuraSlabExtrema MiuraSlabNeutral
open MiuraSlabIncidence MiuraSlabBudget MiuraSlabRunBound MiuraSlabClassification
open MiuraSlabFrozen MiuraSlabSigns MiuraSlabCover MiuraEqualitySaturation MiuraEqualityProfile
variable {m n : ℕ}

private theorem run_equality_charge {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hr : ∃ i, ¬ RowOccupied h i) (hc : ∃ j, ¬ RowOccupied (transposeHeight h) j)
    (heq : (extrema h).card = (frozenRowRunStarts h).card +
      (frozenRowRunStarts (transposeHeight h)).card) :
    (extrema h).card = (neutralRowSlabs h).card + (neutralColSlabs h).card +
      (minRowSlabs h).card * (minColSlabs h).card +
      (maxRowSlabs h).card * (maxColSlabs h).card := by
  have hpartR := row_slab_card_partition hh hm (by omega) hr
  have hpartC := row_slab_card_partition (transpose_isHeight hh) hn (by omega) hc
  have hrow := slab_card_eq_frozen_runs_add_one hh hm (by omega)
  have hcol := slab_card_eq_frozen_runs_add_one (transpose_isHeight hh) hn (by omega)
  have hminR : 1 ≤ (minRowSlabs h).card := (minimum_row_slab_exists hh hm (by omega) hr).card_pos
  have hmaxR : 1 ≤ (maxRowSlabs h).card := (maximum_row_slab_exists hh hm (by omega) hr).card_pos
  have hminC : 1 ≤ (minColSlabs h).card :=
    (minimum_row_slab_exists (transpose_isHeight hh) hn (by omega) hc).card_pos
  have hmaxC : 1 ≤ (maxColSlabs h).card :=
    (maximum_row_slab_exists (transpose_isHeight hh) hn (by omega) hc).card_pos
  have hpm := product_budget (minRowSlabs h).card (minColSlabs h).card hminR hminC
  have hpM := product_budget (maxRowSlabs h).card (maxColSlabs h).card hmaxR hmaxC
  have hb := slab_extremum_budget hh hm (by omega)
  change (rowSlabs (transposeHeight h)).card =
    (minColSlabs h).card + (maxColSlabs h).card + (neutralColSlabs h).card at hpartC
  omega

private theorem row_neutral_interior {h : Cell m n → ℤ} {v : Cell m n}
    (hv : v ∈ rowNeutralSupport h) : 0 < v.1.val ∧ v.1.val + 1 < m := by
  classical
  obtain ⟨I, hI, hvi⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨_, s, hs, ht, hb, _⟩ := Finset.mem_filter.mp hI
  have hvI : I.first.val ≤ v.1.val ∧ v.1.val ≤ I.last.val := (Finset.mem_filter.mp hvi).2
  omega

private theorem col_neutral_interior {h : Cell m n → ℤ} {v : Cell m n}
    (hv : v ∈ colNeutralSupport h) : 0 < v.2.val ∧ v.2.val + 1 < n := by
  classical
  obtain ⟨I, hI, hvi⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨_, s, hs, ht, hb, _⟩ := Finset.mem_filter.mp hI
  have hvI : I.first.val ≤ v.2.val ∧ v.2.val ≤ I.last.val := (Finset.mem_filter.mp hvi).2
  omega

/-- At equality of the actual frozen-run bound, every neutral-row extremum
is strictly internal on both physical axes. -/
theorem equality_neutral_extremum_interior {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hr : ∃ i, ¬ RowOccupied h i) (hc : ∃ j, ¬ RowOccupied (transposeHeight h) j)
    (heq : (extrema h).card = (frozenRowRunStarts h).card +
      (frozenRowRunStarts (transposeHeight h)).card)
    (v : Cell m n) (hv : v ∈ rowNeutralSupport h) :
    0 < v.1.val ∧ v.1.val + 1 < m ∧ 0 < v.2.val ∧ v.2.val + 1 < n := by
  have hs := (frozen_run_equality_incidence hh hm hn hr hc heq).1
  have hri := row_neutral_interior hv
  have hci := col_neutral_interior (hs ▸ hv)
  exact ⟨hri.1, hri.2, hci.1, hci.2⟩

private theorem profile_max_of_shift {h : Cell m n → ℤ} (i k : Fin m) (c : ℤ)
    (he : ∀ j : Fin n, h (i, j) = h (k, j) + c) (j : Fin n) :
    IsStrictLocalMax (profile h i) (0, j) ↔ IsStrictLocalMax (profile h k) (0, j) := by
  constructor <;> intro hp u hu
  · have hv := hp u hu
    change h (i, u.2) = h (i, j) - 1 at hv
    change h (k, u.2) = h (k, j) - 1
    rw [he u.2, he j] at hv
    omega
  · have hv := hp u hu
    change h (k, u.2) = h (k, j) - 1 at hv
    change h (i, u.2) = h (i, j) - 1
    rw [he u.2, he j]
    omega

private theorem neg_height {h : Cell m n → ℤ} (hh : IsHeight h) :
    IsHeight (fun v => -h v) := by
  intro v u hu
  simpa only [neg_sub_neg, abs_sub_comm] using hh v u hu

/-- The finite one-exit theorem makes an actual minimum-free prefix a
uniform descending extrusion, including its final exit row. -/
private theorem prefix_without_minimum {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 0 < m) (i : Fin m)
    (hno : ∀ v : Cell m n, v.1.val < i.val → ¬ IsStrictLocalMin h v)
    (j : Fin n) : h (i, j) = h (⟨0, hm⟩, j) - (i.val : ℤ) := by
  have hpr : 0 + (i.val + 1) ≤ m := by have := i.isLt; omega
  have hrig := one_exit_strip_rigid (neg_height hh) 0 (i.val + 1) (by omega) hpr
    (by
      intro v hv hmax
      apply hno (stripMap 0 (i.val + 1) hpr v) (by
        change 0 + v.1.val < i.val; omega)
      intro u hu
      have := hmax u hu
      dsimp at this
      omega)
    (by intro v u hu hlo; omega) ((0, j) : Cell (i.val + 1) n)
  have hzero : stripMap 0 (i.val + 1) hpr ((0, j) : Cell (i.val + 1) n) =
      ((⟨0, hm⟩, j) : Cell m n) := Prod.ext (Fin.ext (by simp [stripMap])) rfl
  have hlast : stripMap 0 (i.val + 1) hpr
      ((⟨i.val + 1 - 1, by omega⟩, j) : Cell (i.val + 1) n) = (i, j) :=
    Prod.ext (Fin.ext (by simp [stripMap])) rfl
  rw [hzero, hlast] at hrig
  simp only [Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero] at hrig
  omega

/-- If the physical top profile has one peak, the first actual minimum
row can only begin in a minimum-type slab at equality of the run bound. -/
theorem equality_first_minimum_in_minimum_slab {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hr : ∃ i, ¬ RowOccupied h i) (hc : ∃ j, ¬ RowOccupied (transposeHeight h) j)
    (heq : (extrema h).card = (frozenRowRunStarts h).card +
      (frozenRowRunStarts (transposeHeight h)).card)
    (hu : ∃! p : Fin n, IsStrictLocalMax (profile h ⟨0, by omega⟩) (0, p))
    (v : Cell m n) (hv : IsStrictLocalMin h v)
    (hfirst : ∀ u : Cell m n, u.1.val < v.1.val → ¬ IsStrictLocalMin h u) :
    ∃ I ∈ minRowSlabs h, I.Contains v.1 := by
  classical
  have hshift (j : Fin n) : h (v.1, j) = h (⟨0, by omega⟩, j) + -(v.1.val : ℤ) := by
    have he := prefix_without_minimum hh (by omega) v.1 hfirst j
    omega
  have hiff := profile_max_of_shift v.1 (⟨0, by omega⟩ : Fin m) (-(v.1.val : ℤ)) hshift
  have hup : ∃! p : Fin n, IsStrictLocalMax (profile h v.1) (0, p) := by
    obtain ⟨p, hp, hpu⟩ := hu
    exact ⟨p, (hiff p).mpr hp, fun q hq => hpu q ((hiff q).mp hq)⟩
  have hprof : IsStrictLocalMin (profile h v.1) (0, v.2) := by
    intro u hu
    apply hv (v.1, u.2)
    simp only [adj, gdist] at hu ⊢
    omega
  have hb := unique_profile_peak_minima_on_boundary hh v.1 hup v.2 hprof
  have hnc : v ∉ colNeutralSupport h := by
    intro hc
    have hi := col_neutral_interior hc
    omega
  have hs := (frozen_run_equality_incidence hh hm hn hr hc heq).1
  have hnr : v ∉ rowNeutralSupport h := by
    intro hvn
    have hi := equality_neutral_extremum_interior hh hm hn hr hc heq v hvn
    omega
  have hnot : v ∉ neutralSupport h := by
    simp only [neutralSupport, Finset.mem_union, not_or]
    exact ⟨hnr, hnc⟩
  have he := run_equality_charge hh hm hn hr hc heq
  have hev : v ∈ extrema h := by simp [extrema, hv]
  rcases equality_nonneutral_extremum hh hm (by omega) he v hev hnot with
    ⟨I, hI, J, hJ, hvI, _⟩ | ⟨I, hI, J, hJ, hvI, hvJ, hmax⟩
  · exact ⟨I, hI, hvI⟩
  · have hminmax := hv
    let u : Cell m n := (if v.1.val = 0 then ⟨1, by omega⟩ else
      ⟨v.1.val - 1, by have := v.1.isLt; omega⟩, v.2)
    have ha : adj v u := by
      dsimp [u]; split <;> simp only [adj, gdist] <;> omega
    have := hv u ha
    have := hmax u ha
    omega

private theorem minimum_boundary_from_shift {h : Cell m n → ℤ} (hh : IsHeight h)
    (i k : Fin m) (c : ℤ) (hshift : ∀ j, h (i, j) = h (k, j) + c)
    (hu : ∃! p : Fin n, IsStrictLocalMax (profile h k) (0, p))
    (j : Fin n) (hj : IsStrictLocalMin h (i, j)) : j.val = 0 ∨ j.val + 1 = n := by
  have hiff := profile_max_of_shift i k c hshift
  have hup : ∃! p : Fin n, IsStrictLocalMax (profile h i) (0, p) := by
    obtain ⟨p, hp, hpu⟩ := hu
    exact ⟨p, (hiff p).mpr hp, fun q hq => hpu q ((hiff q).mp hq)⟩
  apply unique_profile_peak_minima_on_boundary hh i hup j
  intro u hu
  apply hj (i, u.2)
  simp only [adj, gdist] at hu ⊢
  omega

private theorem suffix_without_minimum {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 0 < m) (i : Fin m)
    (hno : ∀ v : Cell m n, i.val < v.1.val → ¬ IsStrictLocalMin h v)
    (j : Fin n) : h (i, j) = h (⟨m - 1, by omega⟩, j) - ((m - 1 - i.val : ℕ) : ℤ) := by
  let g : Cell m n → ℤ := fun v => h (v.1.rev, v.2)
  have hg : IsHeight g := by
    intro v u hu
    apply hh (v.1.rev, v.2) (u.1.rev, u.2)
    simp only [adj, gdist, Fin.val_rev] at hu ⊢
    omega
  have hno' (v : Cell m n) (hv : v.1.val < i.rev.val) : ¬ IsStrictLocalMin g v := by
    intro hmin
    apply hno (v.1.rev, v.2) (by simp only [Fin.val_rev] at hv ⊢; have := i.isLt; have := v.1.isLt; omega)
    intro u hu
    have he := hmin (u.1.rev, u.2) (by
      simp only [adj, gdist, Fin.val_rev] at hu ⊢
      have := u.1.isLt
      omega)
    simpa only [g, Fin.rev_rev] using he
  have he := prefix_without_minimum hg hm i.rev hno' j
  have hz : (⟨0, hm⟩ : Fin m).rev = (⟨m - 1, by omega⟩ : Fin m) :=
    Fin.ext (by simp [Fin.val_rev])
  have hnat : m - (i.val + 1) = m - 1 - i.val := by omega
  simpa only [g, Fin.rev_rev, hz, Fin.val_rev, hnat] using he

private theorem boundary_minimum_in_minimum_slab {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hr : ∃ i, ¬ RowOccupied h i) (hc : ∃ j, ¬ RowOccupied (transposeHeight h) j)
    (heq : (extrema h).card = (frozenRowRunStarts h).card +
      (frozenRowRunStarts (transposeHeight h)).card)
    (v : Cell m n) (hv : IsStrictLocalMin h v) (hb : v.2.val = 0 ∨ v.2.val + 1 = n) :
    ∃ I ∈ minRowSlabs h, I.Contains v.1 := by
  classical
  have hnc : v ∉ colNeutralSupport h := by
    intro hc
    have hi := col_neutral_interior hc
    omega
  have hs := (frozen_run_equality_incidence hh hm hn hr hc heq).1
  have hnr : v ∉ rowNeutralSupport h := by
    intro hvn
    have hi := equality_neutral_extremum_interior hh hm hn hr hc heq v hvn
    omega
  have hnot : v ∉ neutralSupport h := by
    simp only [neutralSupport, Finset.mem_union, not_or]
    exact ⟨hnr, hnc⟩
  have hev : v ∈ extrema h := by simp [extrema, hv]
  rcases equality_nonneutral_extremum hh hm (by omega)
      (run_equality_charge hh hm hn hr hc heq) v hev hnot with
    ⟨I, hI, J, hJ, hvI, _⟩ | ⟨I, hI, J, hJ, hvI, hvJ, hmax⟩
  · exact ⟨I, hI, hvI⟩
  · let u : Cell m n := (if v.1.val = 0 then ⟨1, by omega⟩ else
      ⟨v.1.val - 1, by have := v.1.isLt; omega⟩, v.2)
    have ha : adj v u := by
      dsimp [u]; split <;> simp only [adj, gdist] <;> omega
    have := hv u ha
    have := hmax u ha
    omega

/-- With one actual minimum row slab and single-peaked physical top and
bottom profiles, equality admits no neutral slabs on either axis. All profiles
and all extremum supports belong to the same actual height array. -/
theorem equality_no_neutral_of_boundary_peaks {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hr : ∃ i, ¬ RowOccupied h i) (hc : ∃ j, ¬ RowOccupied (transposeHeight h) j)
    (heq : (extrema h).card = (frozenRowRunStarts h).card +
      (frozenRowRunStarts (transposeHeight h)).card)
    (hmin : (minRowSlabs h).card = 1)
    (htop : ∃! p : Fin n, IsStrictLocalMax (profile h ⟨0, by omega⟩) (0, p))
    (hbottom : ∃! p : Fin n, IsStrictLocalMax (profile h ⟨m - 1, by omega⟩) (0, p)) :
    neutralRowSlabs h = ∅ ∧ neutralColSlabs h = ∅ := by
  classical
  let S := MiuraResidualCount.minima h
  have hS : S.Nonempty := by
    obtain ⟨⟨v, hv, _⟩, _⟩ := envelope_min hh ((⟨0, by omega⟩, ⟨0, by omega⟩) : Cell m n)
    exact ⟨v, by simp [S, MiuraResidualCount.minima, hv]⟩
  obtain ⟨x, hx, hxleast⟩ := Finset.exists_min_image S (fun v => v.1.val) hS
  obtain ⟨y, hy, hygreatest⟩ := Finset.exists_max_image S (fun v => v.1.val) hS
  have hx' : IsStrictLocalMin h x := by simpa [S, MiuraResidualCount.minima] using hx
  have hy' : IsStrictLocalMin h y := by simpa [S, MiuraResidualCount.minima] using hy
  have hfirst (u : Cell m n) (hu : u.1.val < x.1.val) : ¬ IsStrictLocalMin h u := by
    intro hminu
    have huS : u ∈ S := by simp [S, MiuraResidualCount.minima, hminu]
    have := hxleast u huS
    omega
  have hlast (u : Cell m n) (hu : y.1.val < u.1.val) : ¬ IsStrictLocalMin h u := by
    intro hminu
    have huS : u ∈ S := by simp [S, MiuraResidualCount.minima, hminu]
    have := hygreatest u huS
    omega
  obtain ⟨I, hI, hxI⟩ := equality_first_minimum_in_minimum_slab hh hm hn hr hc heq htop x hx' hfirst
  have hshift (j : Fin n) : h (y.1, j) = h (⟨m - 1, by omega⟩, j) +
      -((m - 1 - y.1.val : ℕ) : ℤ) := by
    have he := suffix_without_minimum hh (by omega) y.1 hlast j
    omega
  have hybound := minimum_boundary_from_shift hh y.1 (⟨m - 1, by omega⟩ : Fin m)
    (-((m - 1 - y.1.val : ℕ) : ℤ)) hshift hbottom y.2 hy'
  obtain ⟨J, hJ, hyJ⟩ := boundary_minimum_in_minimum_slab hh hm hn hr hc heq y hy' hybound
  have hJI : J = I := Finset.card_le_one_iff.mp (by omega : (minRowSlabs h).card ≤ 1) hJ hI
  subst J
  have hrow : neutralRowSlabs h = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro K hK
    obtain ⟨hKs, s, hs, hcuts⟩ := Finset.mem_filter.mp hK
    have hKs' : IsRowSlab h K := (Finset.mem_filter.mp hKs).2
    obtain ⟨⟨v, hvK, hvm⟩, _⟩ := neutral_row_has_both hh K s hs hcuts
      ⟨K.first, ⟨le_rfl, K.ordered⟩, hKs'.1 K.first ⟨le_rfl, K.ordered⟩⟩
    have hvS : v ∈ S := by simp [S, MiuraResidualCount.minima, hvm]
    have hxv := hxleast v hvS
    have hyv := hygreatest v hvS
    have hvI : I.Contains v.1 := by
      change I.first.val ≤ v.1.val ∧ v.1.val ≤ I.last.val
      change I.first.val ≤ x.1.val ∧ x.1.val ≤ I.last.val at hxI
      change I.first.val ≤ y.1.val ∧ y.1.val ≤ I.last.val at hyJ
      omega
    have hIK : I = K := row_slab_unique
      (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2 hKs' v.1 hvI hvK
    subst K
    exact neutral_not_outward (by omega) I s 1 (by norm_num) hcuts (Finset.mem_filter.mp hI).2.2
  have hcounts := (frozen_run_equality_incidence hh hm hn hr hc heq).2.1
  have hcol : neutralColSlabs h = ∅ := Finset.card_eq_zero.mp (by rw [hrow] at hcounts; simpa using hcounts.symm)
  exact ⟨hrow, hcol⟩

private theorem top_profile_max_ambient {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hno : ∀ j : Fin n, ¬ IsStrictLocalMin h (⟨0, by omega⟩, j))
    (j : Fin n) (hj : IsStrictLocalMax (profile h ⟨0, by omega⟩) (0, j)) :
    IsStrictLocalMax h (⟨0, by omega⟩, j) := by
  have hd (k : Fin n) : h (⟨1, by omega⟩, k) = h (⟨0, by omega⟩, k) - 1 := by
    apply prefix_without_minimum hh (by omega) (⟨1, by omega⟩ : Fin m) ?_ k
    intro v hv hmin
    change v.1.val < 1 at hv
    have he : v.1 = (⟨0, by omega⟩ : Fin m) := Fin.ext (by change v.1.val = 0; omega)
    exact hno v.2 (he ▸ hmin)
  intro u hu
  change h (u.1, u.2) = _
  rcases adj_row_or_col hu with ⟨hr, hc⟩ | ⟨hc, hr⟩
  · have hur : u.1 = (⟨0, by omega⟩ : Fin m) := hr.symm
    have he := hj ((0, u.2) : Cell 1 n) (by
      change ((j.val : ℤ) - u.2.val).natAbs = 1 at hc
      simp only [adj, gdist, Fin.val_zero, sub_self, Int.natAbs_zero, zero_add]
      exact_mod_cast hc)
    simpa only [profile, hur] using he
  · have hur : u.1 = (⟨1, by omega⟩ : Fin m) := Fin.ext (by
      change ((0 : ℤ) - u.1.val).natAbs = 1 at hr
      change u.1.val = 1
      omega)
    change j = u.2 at hc
    simpa only [hur, ← hc] using hd j

private theorem bottom_profile_max_ambient {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hno : ∀ j : Fin n, ¬ IsStrictLocalMin h (⟨m - 1, by omega⟩, j))
    (j : Fin n) (hj : IsStrictLocalMax (profile h ⟨m - 1, by omega⟩) (0, j)) :
    IsStrictLocalMax h (⟨m - 1, by omega⟩, j) := by
  have hd (k : Fin n) : h (⟨m - 2, by omega⟩, k) = h (⟨m - 1, by omega⟩, k) - 1 := by
    have he := suffix_without_minimum hh (by omega) (⟨m - 2, by omega⟩ : Fin m) (by
      intro v hv hmin
      have he : v.1 = (⟨m - 1, by omega⟩ : Fin m) := Fin.ext (by
        change v.1.val = m - 1; have := v.1.isLt; change m - 2 < v.1.val at hv; omega)
      exact hno v.2 (he ▸ hmin)) k
    have hn : m - 1 - (m - 2) = 1 := by omega
    simpa only [Fin.val_mk, hn, Nat.cast_one] using he
  intro u hu
  change h (u.1, u.2) = _
  rcases adj_row_or_col hu with ⟨hr, hc⟩ | ⟨hc, hr⟩
  · have hur : u.1 = (⟨m - 1, by omega⟩ : Fin m) := hr.symm
    have he := hj ((0, u.2) : Cell 1 n) (by
      change ((j.val : ℤ) - u.2.val).natAbs = 1 at hc
      simp only [adj, gdist, Fin.val_zero, sub_self, Int.natAbs_zero, zero_add]
      exact_mod_cast hc)
    simpa only [profile, hur] using he
  · have hur : u.1 = (⟨m - 2, by omega⟩ : Fin m) := Fin.ext (by
      change ((((m - 1 : ℕ) : ℤ) - u.1.val).natAbs) = 1 at hr
      change u.1.val = m - 2
      have := u.1.isLt
      omega)
    change j = u.2 at hc
    simpa only [hur, ← hc] using hd j

private theorem profile_unique_of_unique_ambient {h : Cell m n → ℤ} (hh : IsHeight h)
    (hn : 0 < n) (i : Fin m) (I : Interval m) (hi : I.Contains i)
    (hlift : ∀ j : Fin n, IsStrictLocalMax (profile h i) (0, j) → IsStrictLocalMax h (i, j))
    (huniq : ∃! v : Cell m n, I.Contains v.1 ∧ IsStrictLocalMax h v) :
    ∃! p : Fin n, IsStrictLocalMax (profile h i) (0, p) := by
  obtain ⟨⟨q, hq, _⟩, _⟩ := envelope_max (profile_isHeight hh i) ((0, ⟨0, hn⟩) : Cell 1 n)
  have hqzero : q.1 = (0 : Fin 1) := Subsingleton.elim _ _
  have hq' : IsStrictLocalMax (profile h i) (0, q.2) := (Prod.ext hqzero rfl : q = (0, q.2)) ▸ hq
  obtain ⟨v, hv, hvuniq⟩ := huniq
  refine ⟨q.2, hq', ?_⟩
  intro p hp
  have hpv := hvuniq (i, p) ⟨hi, hlift p hp⟩
  have hqv := hvuniq (i, q.2) ⟨hi, hlift q.2 hq'⟩
  exact congrArg Prod.snd (hpv.trans hqv.symm)

/-- The single-peak hypotheses needed for crossed-pattern rigidity are
derived from actual boundary maximum slabs and a single maximum column slab. -/
theorem equality_boundary_maximum_profiles {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hr : ∃ i, ¬ RowOccupied h i) (hc : ∃ j, ¬ RowOccupied (transposeHeight h) j)
    (heq : (extrema h).card = (frozenRowRunStarts h).card +
      (frozenRowRunStarts (transposeHeight h)).card)
    (hmaxcol : (maxColSlabs h).card = 1)
    (I J : Interval m) (hI : I ∈ maxRowSlabs h) (hJ : J ∈ maxRowSlabs h)
    (ht : I.Contains ⟨0, by omega⟩) (hb : J.Contains ⟨m - 1, by omega⟩) :
    (∃! p : Fin n, IsStrictLocalMax (profile h ⟨0, by omega⟩) (0, p)) ∧
    (∃! p : Fin n, IsStrictLocalMax (profile h ⟨m - 1, by omega⟩) (0, p)) := by
  have he := run_equality_charge hh hm hn hr hc heq
  have hsign := (equality_slab_extrema_sign hh hm (by omega) he).2
  constructor
  · apply profile_unique_of_unique_ambient hh (by omega) _ I ht
      (top_profile_max_ambient hh hm (fun j => hsign I hI _ ht))
    exact equality_maximum_slab_unique hh hm (by omega) he hmaxcol I hI
  · apply profile_unique_of_unique_ambient hh (by omega) _ J hb
      (bottom_profile_max_ambient hh hm (fun j => hsign J hJ _ hb))
    exact equality_maximum_slab_unique hh hm (by omega) he hmaxcol J hJ

/-- Actual crossed-pattern boundary slabs exclude all neutral slabs. -/
theorem equality_crossed_no_neutral {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hr : ∃ i, ¬ RowOccupied h i) (hc : ∃ j, ¬ RowOccupied (transposeHeight h) j)
    (heq : (extrema h).card = (frozenRowRunStarts h).card +
      (frozenRowRunStarts (transposeHeight h)).card)
    (hminrow : (minRowSlabs h).card = 1) (hmaxcol : (maxColSlabs h).card = 1)
    (I J : Interval m) (hI : I ∈ maxRowSlabs h) (hJ : J ∈ maxRowSlabs h)
    (ht : I.Contains ⟨0, by omega⟩) (hb : J.Contains ⟨m - 1, by omega⟩) :
    neutralRowSlabs h = ∅ ∧ neutralColSlabs h = ∅ := by
  obtain ⟨htop, hbottom⟩ := equality_boundary_maximum_profiles hh hm hn hr hc heq hmaxcol I J hI hJ ht hb
  exact equality_no_neutral_of_boundary_peaks hh hm hn hr hc heq hminrow htop hbottom

end D5.S3.Combinatorics.Geometry.MiuraEqualityNeutral
