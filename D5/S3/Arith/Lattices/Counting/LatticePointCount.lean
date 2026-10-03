/- GID: D5/S3/Arith/Lattices/Counting/LatticePointCount
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Counting/LatticePointCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The lattice grid-count error is bounded by the number of grid cells meeting the frontier. -/
module

public import Mathlib.Analysis.BoxIntegral.UnitPartition
public import Mathlib.Data.Pi.Interval
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Effective lattice-point count with a Lipschitz-boundary error term

The effective (with explicit `O(tᵈ⁻¹)` rate) strengthening of
`tendsto_card_div_pow_atTop_volume`: for a bounded measurable region whose boundary is
covered by finitely many Lipschitz images of the unit cube, the number of points of the
scaled integer lattice inside the region equals the volume times `nᵈ` up to `O(nᵈ⁻¹)`.

This is the single deepest analytic input to the class-field-theory-free formalisation of
Chebotarev's density theorem: it upgrades the leading-term ideal count to an effective count
with a power-saving error, hence the analytic continuation of the abelian `L`-functions past
`Re s = 1`. It is stated here for a future mathlib contribution.

## Strategy

Following the boundary-cell argument of Lang, GTM 110 Ch. VI §3 Theorem 3 (p. 129) and
Widmer / Gun–Ramaré–Sivaraman: the number of points of the scaled lattice `n⁻¹·ℤ^ι` in `s`
differs from `vol(s)·nᵈ` by at most the number of grid cells of the `n⁻¹ℤ^ι` grid that meet
the frontier `∂s` (`abs_card_inter_sub_volume_mul_pow_le`).

## Main results

* `Chebotarev.abs_card_inter_sub_volume_mul_pow_le`,
  `Chebotarev.ncard_index_image_le_of_diam_le`,
  `Chebotarev.setFinite_index_image_of_isBounded`: building blocks reused by the unit-grid
  ideal-congruence count.

## References

* Serge Lang, *Algebraic Number Theory*, 2nd ed., GTM 110, Springer 1994, Ch. V §2 and
  Ch. VI §3 (Theorem 3), p. 129 (the boundary-cell estimate).
* S. Gun, O. Ramaré, J. Sivaraman, *Counting ideals in ray classes*, J. Number Theory 243
  (2023) 13–37, §3.3 (Lipschitz class of the boundary) and §3.5 (counting points), after
  K. Debaene.
-/

open Submodule Pointwise MeasureTheory Set BoxIntegral.unitPartition

open scoped NNReal

namespace Chebotarev

@[expose] public section

section Sublemmas

variable {ι : Type*} [Fintype ι]

-- The `Fintype ι` instance is needed for the `sup`-metric on `ι → ℝ`, so the
-- `unusedFintypeInType` linter (which only inspects the conclusion) is a false positive here.
/-- The `index n`-image of a bounded set is finite: only finitely many cells of the `n⁻¹ℤ^ι`
grid meet a bounded set. -/
theorem setFinite_index_image_of_isBounded (n : ℕ) {T : Set (ι → ℝ)}
    (hbdd : Bornology.IsBounded T) : (index n '' T).Finite := by
  classical
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall (0 : ι → ℝ)
  set F : Finset (ι → ℤ) :=
    Fintype.piFinset fun _ : ι ↦ Finset.Icc (⌈-((n : ℝ) * R)⌉ - 1) (⌈(n : ℝ) * R⌉ - 1) with hF
  refine Set.Finite.subset (Finset.finite_toSet F) ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only [hF, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc, index_apply]
  intro i
  have hxi : |x i| ≤ R := by
    have hd : dist (x i) ((0 : ι → ℝ) i) ≤ dist x 0 := dist_le_pi_dist x 0 i
    rw [Real.dist_eq, Pi.zero_apply, sub_zero] at hd
    exact hd.trans (by simpa [Real.dist_eq] using hR hx)
  rcases abs_le.mp hxi with ⟨hlo, hhi⟩
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  exact ⟨sub_le_sub_right (Int.ceil_le_ceil (by nlinarith)) 1,
    sub_le_sub_right (Int.ceil_le_ceil (by nlinarith)) 1⟩

/-- **Bounded-diameter cell incidence.** A set `T ⊆ ι → ℝ` of diameter `≤ r` meets at most
`(2⌈n·r⌉₊ + 1)ᵈ` cells of the `n⁻¹ℤ^ι` grid, i.e. its `index n`-image has at most that many
points. (Here `ι → ℝ` carries the sup metric, so a cube of side `1/n` has diameter `1/n`.) -/
theorem ncard_index_image_le_of_diam_le (n : ℕ) [NeZero n] {T : Set (ι → ℝ)} {r : ℝ}
    (hr : 0 ≤ r) (hdiam : Metric.diam T ≤ r) (hbdd : Bornology.IsBounded T) :
    (index n '' T).ncard ≤ (2 * ⌈(n : ℝ) * r⌉₊ + 1) ^ Fintype.card ι := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp only [image_empty, ncard_empty, zero_le]
  set K : ℕ := ⌈(n : ℝ) * r⌉₊ with hK
  set c : ι → ℤ := index n x₀ with hc
  set F : Finset (ι → ℤ) := Fintype.piFinset fun i ↦ Finset.Icc (c i - K) (c i + K) with hF
  have hsub : index n '' T ⊆ ↑F := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [hF, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have hdx : |x i - x₀ i| ≤ r := by
      have h1 : dist (x i) (x₀ i) ≤ dist x x₀ := dist_le_pi_dist x x₀ i
      rw [Real.dist_eq] at h1
      exact h1.trans ((Metric.dist_le_diam_of_mem hbdd hx hx₀).trans hdiam)
    rcases abs_le.mp hdx with ⟨hlo, hhi⟩
    have hKeq : (K : ℤ) = ⌈(n : ℝ) * r⌉ := hK ▸ Int.natCast_ceil_eq_ceil (by positivity)
    have hub : (⌈(n : ℝ) * x i⌉ : ℤ) ≤ ⌈(n : ℝ) * x₀ i⌉ + ⌈(n : ℝ) * r⌉ :=
      calc
        (⌈(n : ℝ) * x i⌉ : ℤ) ≤ ⌈(n : ℝ) * x₀ i + (n : ℝ) * r⌉ :=
          Int.ceil_le_ceil (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
        _ ≤ ⌈(n : ℝ) * x₀ i⌉ + ⌈(n : ℝ) * r⌉ := Int.ceil_add_le _ _
    have hlb : (⌈(n : ℝ) * x₀ i⌉ : ℤ) ≤ ⌈(n : ℝ) * x i⌉ + ⌈(n : ℝ) * r⌉ :=
      calc
        (⌈(n : ℝ) * x₀ i⌉ : ℤ) ≤ ⌈(n : ℝ) * x i + (n : ℝ) * r⌉ :=
          Int.ceil_le_ceil (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
        _ ≤ ⌈(n : ℝ) * x i⌉ + ⌈(n : ℝ) * r⌉ := Int.ceil_add_le _ _
    simp only [index_apply, hc]
    constructor <;> lia
  refine (Set.ncard_le_ncard hsub F.finite_toSet).trans ?_
  rw [Set.ncard_coe_finset, hF, Fintype.card_piFinset]
  have hcard : ∀ i, (Finset.Icc (c i - K) (c i + K)).card = 2 * K + 1 := by
    intro i
    rw [Int.card_Icc]
    lia
  rw [Finset.prod_congr rfl fun i _ ↦ hcard i, Finset.prod_const, Finset.card_univ]

/-- **Count ↔ volume bridge.** The number of points of `n⁻¹ℤ^ι` in a bounded measurable `s`
differs from `vol(s)·nᵈ` by at most the number of grid cells meeting `∂s`. This is the
effective form of the sandwich behind `tendsto_card_div_pow_atTop_volume`. -/
theorem abs_card_inter_sub_volume_mul_pow_le {s : Set (ι → ℝ)}
    (hbdd : Bornology.IsBounded s) (hmeas : MeasurableSet s) {n : ℕ} (hn : 1 ≤ n) :
    |(Nat.card ↑(s ∩ (n : ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) : ℝ)
        - volume.real s * (n : ℝ) ^ Fintype.card ι|
      ≤ (index n '' frontier s).ncard := by
  classical
  have hne : NeZero n := ⟨Nat.one_le_iff_ne_zero.mp hn⟩
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hne.out
  have hvs : volume s ≠ ⊤ := hbdd.measure_lt_top.ne
  set Inside : Set (ι → ℤ) := {ν | (box n ν : Set (ι → ℝ)) ⊆ s}
  set Meet : Set (ι → ℤ) := {ν | ((box n ν : Set (ι → ℝ)) ∩ s).Nonempty}
  set Bd : Set (ι → ℤ) := index n '' frontier s
  have hInsideFin : Inside.Finite := setFinite_index n hmeas.nullMeasurableSet hvs
  have hBdFin : Bd.Finite :=
    setFinite_index_image_of_isBounded n (hbdd.closure.subset frontier_subset_closure)
  have hMeetSub : Meet ⊆ index n '' s := by
    rintro ν ⟨x, hxb, hxs⟩
    exact ⟨x, hxs, mem_box_iff_index.mp hxb⟩
  have hMeetFin : Meet.Finite :=
    (setFinite_index_image_of_isBounded n hbdd).subset hMeetSub
  set Tag : Set (ι → ℤ) := {ν | tag n ν ∈ s} with hTag
  have himg : index n '' (s ∩ (n : ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) = Tag := by
    ext ν
    simp only [hTag, Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, ⟨hxs, hxL⟩, rfl⟩
      rwa [tag_index_eq_self_of_mem_smul_span n hxL]
    · intro hν
      exact ⟨tag n ν, ⟨hν, tag_mem_smul_span n ν⟩, index_tag n ν⟩
  have hNeq : Nat.card ↑(s ∩ (n : ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) = Tag.ncard := by
    rw [Nat.card_coe_set_eq, ← himg]
    refine (Set.InjOn.ncard_image ?_).symm
    intro x hx y hy h
    exact eq_of_mem_smul_span_of_index_eq_index n hx.2 hy.2 h
  have hIT : Inside ⊆ Tag := fun ν hν ↦ hν (tag_mem n ν)
  have hTM : Tag ⊆ Meet := fun ν hν ↦ ⟨tag n ν, tag_mem n ν, hν⟩
  have hMIB : Meet ⊆ Inside ∪ Bd := by
    intro ν hν
    by_cases hsub : (box n ν : Set (ι → ℝ)) ⊆ s
    · exact Or.inl hsub
    · right
      have hconn : IsPreconnected (box n ν : Set (ι → ℝ)) := by
        rw [BoxIntegral.Box.coe_eq_pi]
        exact (convex_pi fun _ _ ↦ convex_Ioc _ _).isPreconnected
      obtain ⟨xc, hxcb, hxcs⟩ : ((box n ν : Set (ι → ℝ)) ∩ sᶜ).Nonempty := by
        rw [Set.not_subset] at hsub
        exact hsub.imp fun _ ⟨hx, hxs⟩ ↦ ⟨hx, hxs⟩
      by_contra hcon
      have hcon' : (box n ν : Set (ι → ℝ)) ∩ frontier s = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨hxb, hxf⟩
        exact hcon ⟨x, hxf, mem_box_iff_index.mp hxb⟩
      have hsplit : (box n ν : Set (ι → ℝ)) ⊆ interior s ∪ (closure s)ᶜ := by
        intro x hx
        by_contra hxc
        rw [Set.mem_union, not_or, Set.notMem_compl_iff] at hxc
        exact (Set.eq_empty_iff_forall_notMem.mp hcon' x) ⟨hx, hxc.2, hxc.1⟩
      rcases hconn.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl
        (disjoint_compl_right_iff_subset.mpr (interior_subset.trans subset_closure)) hsplit
        with hsub' | hsub'
      · exact hxcs (interior_subset (hsub' hxcb))
      · obtain ⟨x, hxb, hxs⟩ := hν
        exact (hsub' hxb) (subset_closure hxs)
  have hcard_IT : Inside.ncard ≤ Tag.ncard :=
    Set.ncard_le_ncard hIT (hMeetFin.subset hTM)
  have hcard_TM : Tag.ncard ≤ Meet.ncard := Set.ncard_le_ncard hTM hMeetFin
  have hcard_MIB : Meet.ncard ≤ Inside.ncard + Bd.ncard :=
    (Set.ncard_le_ncard hMIB (hInsideFin.union hBdFin)).trans (Set.ncard_union_le _ _)
  set V : ℝ := volume.real s * (n : ℝ) ^ Fintype.card ι with hV
  have hnpow : (0 : ℝ) < (n : ℝ) ^ Fintype.card ι := by positivity
  have hcardI : (hInsideFin.toFinset).card = Inside.ncard :=
    (Set.ncard_eq_toFinset_card _ hInsideFin).symm
  have hcardM : (hMeetFin.toFinset).card = Meet.ncard :=
    (Set.ncard_eq_toFinset_card _ hMeetFin).symm
  have hmeasureReal_biUnion_box (t : Finset (ι → ℤ)) :
      volume.real (⋃ ν ∈ t, (box n ν : Set (ι → ℝ))) =
        t.card / (n : ℝ) ^ Fintype.card ι := by
    have hvol_box : ∀ ν : ι → ℤ,
        volume.real (box n ν : Set (ι → ℝ)) = 1 / (n : ℝ) ^ Fintype.card ι := by
      intro ν
      rw [measureReal_def, volume_box]
      simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast]
    rw [measureReal_biUnion_finset (fun ν _ ν' _ h ↦ disjoint.mp h)
      (fun ν _ ↦ (box n ν).measurableSet_coe) (fun ν _ ↦ (box n ν).isBounded.measure_lt_top.ne)]
    simp_rw [hvol_box]
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  have hvol_lower : (Inside.ncard : ℝ) ≤ V := by
    have hsub : (⋃ ν ∈ hInsideFin.toFinset, (box n ν : Set (ι → ℝ))) ⊆ s :=
      Set.iUnion₂_subset fun ν hν ↦ hInsideFin.mem_toFinset.mp hν
    have hle := measureReal_mono hsub hvs
    rw [hmeasureReal_biUnion_box hInsideFin.toFinset, hcardI, div_le_iff₀ hnpow] at hle
    rw [hV]
    linarith
  have hvol_upper : V ≤ (Meet.ncard : ℝ) := by
    have hsub : s ⊆ ⋃ ν ∈ hMeetFin.toFinset, (box n ν : Set (ι → ℝ)) := by
      intro x hxs
      refine Set.mem_iUnion₂.mpr ⟨index n x, hMeetFin.mem_toFinset.mpr ?_,
        mem_box_iff_index.mpr rfl⟩
      exact ⟨x, mem_box_iff_index.mpr rfl, hxs⟩
    have hfinU : volume (⋃ ν ∈ hMeetFin.toFinset, (box n ν : Set (ι → ℝ))) ≠ ⊤ :=
      (measure_biUnion_finset_le _ _).trans_lt (by
        simp only [volume_box]
        exact ENNReal.sum_lt_top.mpr fun _ _ ↦ by finiteness) |>.ne
    have hle := measureReal_mono hsub hfinU
    rw [hmeasureReal_biUnion_box hMeetFin.toFinset, hcardM, le_div_iff₀ hnpow] at hle
    rw [hV]
    linarith
  have hITr : (Inside.ncard : ℝ) ≤ (Tag.ncard : ℝ) := by exact_mod_cast hcard_IT
  have hMIBr : (Meet.ncard : ℝ) ≤ (Inside.ncard : ℝ) + (Bd.ncard : ℝ) := by
    exact_mod_cast hcard_MIB
  have hTMr : (Tag.ncard : ℝ) ≤ (Meet.ncard : ℝ) := by exact_mod_cast hcard_TM
  rw [hNeq, abs_le]
  exact ⟨by linarith, by linarith⟩

end Sublemmas

end

end Chebotarev
