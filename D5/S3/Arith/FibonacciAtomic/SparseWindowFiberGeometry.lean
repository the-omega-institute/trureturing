/- GID: D5/S3/Arith/FibonacciAtomic/SparseWindowFiberGeometry
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SparseWindowFiberGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sparse window fibres are the components between translated circle cuts. -/

import D5.S1.Digit.Infinite.SparseWindowMutualDetermination
import D5.S1.Phase.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Data.Finset.Max
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Algebra.Group.SubmonoidClosure

set_option autoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.SparseWindowFiberGeometry

open D5.S1.Digit.Infinite.SuccessorContinuity
open D5.S1.Digit.Infinite.SignedSeriesRange
open D5.S1.Digit.Infinite.WindowCylinderPartition
open D5.S1.Digit.Infinite.WindowSuccessorGraph
open D5.S1.Digit.Infinite.SparseWindowMutualDetermination
open D5.S1.Phase
open Set Function Topology

local notation "Circle" => AddCircle (1 : ℝ)

/-- The points giving the specified window label at every retained time. -/
noncomputable def fiber (m : ℕ) (S : Finset ℕ) (p : (t : S) → X m) : Set Circle :=
  {z | ∀ t : S, z + goldenPhase (t.val : ℤ) ∈ A (p t)}

/-- The circle with all translated window cuts removed. -/
noncomputable def regularDomain (m : ℕ) (S : Finset ℕ) : Set Circle :=
  (E '' (↑(cuts m S) : Set ℕ))ᶜ

private theorem short_family_preconnected {ι : Type*} (lo hi shift : ι → ℝ)
    (anchor : ι) (hlen : ∀ i, hi anchor - lo anchor + (hi i - lo i) ≤ 1) :
    IsPreconnected {z : Circle | ∀ i,
      z + ((shift i : ℝ) : Circle) ∈
        (fun x : ℝ => (x : Circle)) '' Ioo (lo i) (hi i)} := by
  let lifted : Set ℝ := {x | x ∈ Ioo (lo anchor) (hi anchor) ∧ ∀ i,
    ((x + (shift i - shift anchor) : ℝ) : Circle) ∈
      (fun y : ℝ => (y : Circle)) '' Ioo (lo i) (hi i)}
  have hconvex : lifted.OrdConnected := by
    rw [Set.ordConnected_iff]
    intro x hx y hy hxy v hv
    refine ⟨⟨lt_of_lt_of_le hx.1.1 hv.1, lt_of_le_of_lt hv.2 hy.1.2⟩, ?_⟩
    intro i
    obtain ⟨xx, hxx, hcx⟩ := hx.2 i
    obtain ⟨yy, hyy, hcy⟩ := hy.2 i
    obtain ⟨k, hk'⟩ := circle_integer_offset _ _ hcx.symm
    obtain ⟨j, hj'⟩ := circle_integer_offset _ _ hcy.symm
    have hk := hk'.symm
    have hj := hj'.symm
    have hkj : k = j := by
      have hsmall : (k : ℝ) - j < 1 ∧ (j : ℝ) - k < 1 := by
        constructor <;> linarith only [hx.1.1, hx.1.2, hy.1.1, hy.1.2,
          hxx.1, hxx.2, hyy.1, hyy.2, hlen i, hk, hj]
      have hsmall' : k - j < (1 : ℤ) ∧ j - k < (1 : ℤ) := by
        exact_mod_cast hsmall
      omega
    subst j
    refine ⟨v + (shift i - shift anchor) - k, ⟨?_, ?_⟩, ?_⟩
    · linarith only [hxx.1, hk, hv.1]
    · linarith only [hyy.2, hj, hv.2]
    · have hk0 : ((k : ℝ) : Circle) = 0 :=
        (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k, by simp⟩
      change ((v + (shift i - shift anchor) - k : ℝ) : Circle) = _
      rw [AddCircle.coe_sub, hk0, sub_zero]
  have himage : (fun x : ℝ => (x : Circle) - (shift anchor : Circle)) '' lifted =
      {z : Circle | ∀ i, z + ((shift i : ℝ) : Circle) ∈
        (fun x : ℝ => (x : Circle)) '' Ioo (lo i) (hi i)} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩ i
      change (x : Circle) - (shift anchor : Circle) + (shift i : Circle) ∈ _
      have he : (x : Circle) - (shift anchor : Circle) + (shift i : Circle) =
          ((x + (shift i - shift anchor) : ℝ) : Circle) := by
        simp only [AddCircle.coe_add, AddCircle.coe_sub]
        abel
      rw [he]
      exact hx.2 i
    · intro hz
      obtain ⟨x, hx, hcx⟩ := hz anchor
      change (x : Circle) = z + (shift anchor : Circle) at hcx
      refine ⟨x, ⟨hx, ?_⟩, ?_⟩
      · intro i
        have he : ((x + (shift i - shift anchor) : ℝ) : Circle) =
            z + (shift i : Circle) := by
          rw [AddCircle.coe_add, AddCircle.coe_sub, hcx]
          abel
        rw [he]
        exact hz i
      · change (x : Circle) - (shift anchor : Circle) = z
        rw [hcx]
        abel
  rw [← himage]
  exact hconvex.isPreconnected.image _
    ((AddCircle.continuous_mk' (1 : ℝ)).sub continuous_const).continuousOn

private theorem regular_domain_iff (m : ℕ) (S : Finset ℕ) (z : Circle) :
    z ∈ regularDomain m S ↔ ∀ t : S, z + goldenPhase (t.val : ℤ) ∉ B m := by
  classical
  simp only [goldenPhase, Int.cast_natCast]
  constructor
  · intro hz t ⟨j, hj, he⟩
    rcases hj with ⟨hj1, hjm⟩
    apply hz
    refine ⟨t.val + j, ?_, ?_⟩
    · apply Finset.mem_biUnion.mpr
      exact ⟨t.val, t.property, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
    · exact add_right_cancel ((translated_cut t.val j).trans he)
  · intro hz ⟨k, hk, he⟩
    obtain ⟨t, ht, htk⟩ := Finset.mem_biUnion.mp hk
    have hj : k - t ∈ Icc 1 (G m) := by
      have hh := Finset.mem_Icc.mp htk
      constructor <;> omega
    apply hz ⟨t, ht⟩
    refine ⟨k - t, hj, ?_⟩
    rw [← translated_cut t (k - t), show t + (k - t) = k by
      have := (Finset.mem_Icc.mp htk).1
      omega, he]

private theorem isOpen_fiber (m : ℕ) (S : Finset ℕ) (p : (t : S) → X m) :
    IsOpen (fiber m S p) := by
  classical
  rw [show fiber m S p = ⋂ t : S,
      (fun z : Circle => z + goldenPhase (t.val : ℤ)) ⁻¹' A (p t) by
    ext z
    simp only [fiber, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]]
  apply isOpen_iInter_of_finite
  intro t
  exact (window_arc_isOpen m (p t)).preimage (continuous_id.add continuous_const)

private theorem circle_complement_components_card (T : Finset Circle) (hT : T.Nonempty) :
    Nat.card (ConnectedComponents ↥((↑T : Set Circle)ᶜ)) = T.card := by
  classical
  haveI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨p, hp⟩ := hT
  let a : ℝ := (AddCircle.equivIco (1 : ℝ) 0 p).val
  have hap : (a : Circle) = p := AddCircle.coe_equivIco
  let repr : Circle → ℝ := fun z => (AddCircle.equivIco (1 : ℝ) a z).val
  have hre (z : Circle) : ((repr z : ℝ) : Circle) = z := AddCircle.coe_equivIco
  have hrb (z : Circle) : a ≤ repr z ∧ repr z < a + 1 :=
    (AddCircle.equivIco (1 : ℝ) a z).property
  have hrepr : Function.Injective repr := by
    intro z w h
    exact (hre z).symm.trans ((congrArg (fun x : ℝ => (x : Circle)) h).trans (hre w))
  let R : Finset ℝ := T.image repr
  have haR : a ∈ R := by
    refine Finset.mem_image.mpr ⟨p, hp, ?_⟩
    rw [← hap]
    exact AddCircle.equivIco_coe_of_mem ⟨le_rfl, by linarith⟩
  have hRb (r : ℝ) (hr : r ∈ R) : a ≤ r ∧ r < a + 1 := by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr
    exact hrb z
  let upperGap (r : R) : ℝ :=
    (insert (a + 1) (R.filter (fun s => r.val < s))).min' (Finset.insert_nonempty _ _)
  have hupper (r : R) : r.val < upperGap r ∧ upperGap r ≤ a + 1 ∧
      ∀ s ∈ R, r.val < s → upperGap r ≤ s := by
    refine ⟨?_, ?_, ?_⟩
    · have hm := Finset.min'_mem (insert (a + 1) (R.filter (fun s => r.val < s)))
        (Finset.insert_nonempty _ _)
      rcases Finset.mem_insert.mp hm with he | he
      · simpa only [upperGap, he] using (hRb r.val r.property).2
      · exact (Finset.mem_filter.mp he).2
    · exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)
    · intro s hs hrs
      exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hs, hrs⟩))
  let gap (r : R) : Set Circle := (fun x : ℝ => (x : Circle)) '' Ioo r.val (upperGap r)
  have hsub (r : R) : gap r ⊆ (↑T : Set Circle)ᶜ := by
    rintro z ⟨x, hx, rfl⟩ hz
    have hxI : x ∈ Ico a (a + 1) :=
      ⟨(hRb r.val r.property).1.trans hx.1.le, hx.2.trans_le (hupper r).2.1⟩
    have hxR : x ∈ R := by
      refine Finset.mem_image.mpr ⟨(x : Circle), hz, ?_⟩
      exact AddCircle.equivIco_coe_of_mem hxI
    exact (not_lt_of_ge ((hupper r).2.2 x hxR hx.1)) hx.2
  have hopen (r : R) : IsOpen (gap r) := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hconn (r : R) : IsConnected (gap r) :=
    (isConnected_Ioo (hupper r).1).image _ (AddCircle.continuous_mk' (1 : ℝ)).continuousOn
  have hdisj : Pairwise (Disjoint on gap) := by
    intro r s hrs
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, hxe⟩ ⟨y, hy, hye⟩
    have hxy : x = y := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      ⟨(hRb r.val r.property).1.trans hx.1.le, hx.2.trans_le (hupper r).2.1⟩
      ⟨(hRb s.val s.property).1.trans hy.1.le, hy.2.trans_le (hupper s).2.1⟩).mp
      (hxe.trans hye.symm)
    subst y
    rcases lt_or_gt_of_ne (Subtype.val_injective.ne hrs) with h | h
    · exact (not_lt_of_ge (((hupper r).2.2 s.val s.property h).trans hy.1.le)) hx.2
    · exact (not_lt_of_ge (((hupper s).2.2 r.val r.property h).trans hx.1.le)) hy.2
  have hcover : ∀ z ∈ (↑T : Set Circle)ᶜ, ∃ r : R, z ∈ gap r := by
    intro z hz
    let x := repr z
    have hxR : x ∉ R := by
      intro hx
      obtain ⟨w, hw, hwx⟩ := Finset.mem_image.mp hx
      exact hz (hrepr hwx ▸ hw)
    have hne : (R.filter (fun r => r ≤ x)).Nonempty :=
      ⟨a, Finset.mem_filter.mpr ⟨haR, (hrb z).1⟩⟩
    let r := (R.filter (fun r => r ≤ x)).max' hne
    have hr := Finset.mem_filter.mp (Finset.max'_mem _ hne)
    refine ⟨⟨r, hr.1⟩, x, ⟨lt_of_le_of_ne hr.2 (by intro h; exact hxR (h ▸ hr.1)), ?_⟩,
      hre z⟩
    have hu := Finset.min'_mem (insert (a + 1) (R.filter (fun s => r < s)))
      (Finset.insert_nonempty _ _)
    rcases Finset.mem_insert.mp hu with he | he
    · change x < upperGap ⟨r, hr.1⟩
      dsimp [upperGap]
      rw [he]
      exact (hrb z).2
    · have hs := Finset.mem_filter.mp he
      by_contra h
      have hsx : (upperGap ⟨r, hr.1⟩) ≤ x := le_of_not_gt h
      have hle : (upperGap ⟨r, hr.1⟩) ≤ r :=
        Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hs.1, hsx⟩)
      exact (not_lt_of_ge hle) hs.2
  let D : Set Circle := (↑T : Set Circle)ᶜ
  let U (r : R) : Set D := Subtype.val ⁻¹' gap r
  have hUopen (r : R) : IsOpen (U r) := (hopen r).preimage continuous_subtype_val
  have hUdisj : Pairwise (Disjoint on U) := by
    intro r s h
    exact (hdisj h).preimage Subtype.val
  have hUcover : ⋃ r : R, U r = univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨r, hr⟩ := hcover z.val z.property
    exact Set.mem_iUnion.mpr ⟨r, hr⟩
  have hUclopen (r : R) : IsClopen (U r) := by
    refine ⟨?_, hUopen r⟩
    rw [← isOpen_compl_iff]
    have he : (U r)ᶜ = ⋃ s : {s : R // s ≠ r}, U s.val := by
      ext z
      constructor
      · intro hz
        obtain ⟨s, hs⟩ := hcover z.val z.property
        exact Set.mem_iUnion.mpr ⟨⟨s, by intro he; exact hz (he ▸ hs)⟩, hs⟩
      · intro hz hr
        obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hz
        exact Set.disjoint_left.mp (hUdisj s.property) hs hr
    rw [he]
    exact isOpen_iUnion (fun s => hUopen s.val)
  have hUconn (r : R) : IsConnected (U r) := by
    have he : Subtype.val '' U r = gap r :=
      Set.image_preimage_eq_of_subset (by simpa only [Subtype.range_coe] using hsub r)
    refine ⟨?_, IsInducing.subtypeVal.isPreconnected_image.mp (by rw [he]; exact (hconn r).2)⟩
    obtain ⟨z, hz⟩ := (hconn r).1
    exact ⟨⟨z, hsub r hz⟩, hz⟩
  calc
    Nat.card (ConnectedComponents D) = Nat.card R :=
      Nat.card_congr (ConnectedComponents.equivOfIsClopenOfIsConnected
        hUclopen hUdisj hUcover hUconn)
    _ = R.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = T.card := Finset.card_image_of_injective _ hrepr

/-- For width at least two, every nonempty time tuple fibre is precisely one
connected component of the regular circle domain, and that component determines
the tuple uniquely. Every regular point has a label, the translated cuts have
the specified cardinality, and every nonempty fibre is visited by each natural
golden phase tail. -/
theorem sparse_window_fiber_geometry (m : ℕ) (hm : 2 ≤ m) (S : Finset ℕ)
    (hS : S.Nonempty) :
    (∀ (p : (t : S) → X m) (z : Circle), z ∈ fiber m S p →
      fiber m S p = connectedComponentIn (regularDomain m S) z) ∧
    (∀ (p q : (t : S) → X m) (z w : Circle),
      z ∈ fiber m S p → w ∈ fiber m S q →
      (connectedComponentIn (regularDomain m S) z =
        connectedComponentIn (regularDomain m S) w ↔ p = q)) ∧
    (∀ z ∈ regularDomain m S, ∃! p : (t : S) → X m, z ∈ fiber m S p) ∧
    (E '' (↑(cuts m S) : Set ℕ)).ncard = (cuts m S).card ∧
    (∀ p : (t : S) → X m, (fiber m S p).Nonempty → ∀ bound : ℕ,
      ∃ n : ℕ, bound < n ∧ goldenPhase (n : ℤ) ∈ fiber m S p) ∧
    Nat.card (ConnectedComponents (regularDomain m S)) = (cuts m S).card ∧
    Nat.card (Set.range (sigma m S)) = (cuts m S).card := by
  classical
  have hpos : 0 < alpha := golden_inverse_data.1
  have hlt : alpha < 1 := golden_inverse_data.2.1
  have halpha : alpha ^ 2 + alpha = 1 := golden_inverse_data.2.2
  have hhalf : 1 / 2 < alpha := by
    by_contra h
    have hh : alpha ≤ 1 / 2 := le_of_not_gt h
    have := mul_self_le_mul_self hpos.le hh
    nlinarith
  have hbeta : alpha ^ 2 < 1 / 2 := by linarith
  have hwidth (p : X m) : upper p - ell p ≤ alpha ^ 2 := by
    rw [((window_cylinder_partition.2.2 m (by omega)).2.1 p).2.2.2.2.2.1]
    exact pow_le_pow_of_le_one hpos.le hlt.le (show 2 ≤ d p by dsimp [d]; omega)
  obtain ⟨t0, ht0⟩ := hS
  let anchor : S := ⟨t0, ht0⟩
  have hconnected (p : (t : S) → X m) : IsPreconnected (fiber m S p) := by
    have hlen (t : S) :
        upper (p anchor) - ell (p anchor) + (upper (p t) - ell (p t)) ≤ 1 := by
      linarith [hwidth (p anchor), hwidth (p t)]
    simpa only [fiber, goldenPhase, Int.cast_natCast, A] using
      short_family_preconnected (fun t : S => ell (p t)) (fun t : S => upper (p t))
        (fun t : S => (t.val : ℝ) * Real.goldenRatio) anchor hlen
  have hsubset (p : (t : S) → X m) : fiber m S p ⊆ regularDomain m S := by
    intro z hz
    apply (regular_domain_iff m S z).mpr
    intro t hc
    obtain ⟨k, hk, he⟩ := hc
    exact window_arc_avoids_cut m (by omega) (p t) k hk.1 hk.2 (he.symm ▸ hz t)
  have heq (p : (t : S) → X m) (z : Circle) (hz : z ∈ fiber m S p) :
      fiber m S p = connectedComponentIn (regularDomain m S) z := by
    apply Set.Subset.antisymm
    · exact (hconnected p).subset_connectedComponentIn hz (hsubset p)
    · intro w hw t
      let f : Circle → Circle := fun z => z + goldenPhase (t.val : ℤ)
      let U : Set Circle := f ⁻¹' A (p t)
      let V : Set Circle := ⋃ q : {q : X m // q ≠ p t}, f ⁻¹' A q.val
      have hU : IsOpen U := (window_arc_isOpen m (p t)).preimage
        (continuous_id.add continuous_const)
      have hV : IsOpen V := isOpen_iUnion (fun q =>
        (window_arc_isOpen m q.val).preimage (continuous_id.add continuous_const))
      have hdisjoint : Disjoint U V := by
        apply Set.disjoint_left.mpr
        intro x hx hVx
        obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hVx
        exact q.property (window_arc_unique m (by omega) q.val (p t) (f x) hq hx)
      have hcover : connectedComponentIn (regularDomain m S) z ⊆ U ∪ V := by
        intro x hx
        have hr := (regular_domain_iff m S x).mp
          (connectedComponentIn_subset (regularDomain m S) z hx) t
        obtain ⟨q, hq⟩ := window_arc_cover m (by omega) (f x) hr
        by_cases he : q = p t
        · apply Or.inl
          change f x ∈ A (p t)
          rwa [he] at hq
        · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨q, he⟩, hq⟩)
      exact IsPreconnected.subset_left_of_subset_union hU hV hdisjoint hcover
        ⟨z, mem_connectedComponentIn (hsubset p hz), hz t⟩
        isPreconnected_connectedComponentIn hw
  have hcuts : (cuts m S).Nonempty := by
    refine ⟨t0 + 1, Finset.mem_biUnion.mpr ⟨t0, ht0, Finset.mem_Icc.mpr ⟨le_rfl, ?_⟩⟩⟩
    have hg : 0 < G m := by
      unfold G
      exact Nat.fib_pos.mpr (by omega)
    omega
  have hcomponents : Nat.card (ConnectedComponents (regularDomain m S)) =
      (cuts m S).card := by
    have h := circle_complement_components_card ((cuts m S).image E) (hcuts.image E)
    rw [Finset.coe_image] at h
    exact h.trans (Finset.card_image_of_injective _ cut_injective)
  have hnatural (n : ℕ) (p : (t : S) → X m) :
      sigma m S n = p ↔ goldenPhase (n : ℤ) ∈ fiber m S p := by
    have hcoord (t : S) : q m (n + t.val) = p t ↔
        goldenPhase (n : ℤ) + goldenPhase (t.val : ℤ) ∈ A (p t) := by
      rw [natural_window_arc m (by omega), natural_row_phase]
      simp only [goldenPhase, Nat.cast_add, Int.cast_natCast, add_mul, AddCircle.coe_add]
    constructor
    · intro h t
      exact (hcoord t).mp (congrFun h t)
    · intro h
      funext t
      exact (hcoord t).mpr (h t)
  have hactual (p : (t : S) → X m) : p ∈ Set.range (sigma m S) ↔
      (fiber m S p).Nonempty := by
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨goldenPhase (n : ℤ), (hnatural n _).mp rfl⟩
    · intro hp
      obtain ⟨n, _, hn⟩ := natural_phase_visit (fiber m S p) (isOpen_fiber m S p) hp 0
      exact ⟨n, (hnatural n p).mpr (by simpa only [goldenPhase, Int.cast_natCast] using hn)⟩
  refine ⟨heq, ?_, ?_, ?_, ?_, hcomponents, ?_⟩
  · intro p q z w hz hw
    constructor
    · intro hsame
      have hw' : w ∈ fiber m S p := by
        rw [heq p z hz, hsame]
        exact mem_connectedComponentIn (hsubset q hw)
      funext t
      exact window_arc_unique m (by omega) (p t) (q t)
        (w + goldenPhase (t.val : ℤ)) (hw' t) (hw t)
    · intro hpq
      subst q
      exact (heq p z hz).symm.trans (heq p w hw)
  · intro z hz
    have hc (t : S) : ∃ p : X m, z + goldenPhase (t.val : ℤ) ∈ A p :=
      window_arc_cover m (by omega) _ ((regular_domain_iff m S z).mp hz t)
    refine ⟨fun t => Classical.choose (hc t), fun t => Classical.choose_spec (hc t), ?_⟩
    intro q hq
    funext t
    exact window_arc_unique m (by omega) (q t) (Classical.choose (hc t))
      (z + goldenPhase (t.val : ℤ)) (hq t) (Classical.choose_spec (hc t))
  · rw [Set.ncard_image_of_injective _ cut_injective, Set.ncard_coe_finset]
  · intro p hp bound
    simpa only [goldenPhase, Int.cast_natCast] using
      natural_phase_visit (fiber m S p) (isOpen_fiber m S p) hp bound
  · let U (p : Set.range (sigma m S)) : Set (regularDomain m S) :=
      Subtype.val ⁻¹' fiber m S p.val
    have hUopen (p : Set.range (sigma m S)) : IsOpen (U p) :=
      (isOpen_fiber m S p.val).preimage continuous_subtype_val
    have hUdisj : Pairwise (Disjoint on U) := by
      intro p q hpq
      apply Set.disjoint_left.mpr
      intro z hp hq
      apply hpq
      apply Subtype.ext
      funext t
      exact window_arc_unique m (by omega) (p.val t) (q.val t)
        (z.val + goldenPhase (t.val : ℤ)) (hp t) (hq t)
    have hUcover : ⋃ p : Set.range (sigma m S), U p = univ := by
      apply Set.eq_univ_of_forall
      intro z
      have hc (t : S) : ∃ p : X m, z.val + goldenPhase (t.val : ℤ) ∈ A p :=
        window_arc_cover m (by omega) _ ((regular_domain_iff m S z.val).mp z.property t)
      let p : (t : S) → X m := fun t => Classical.choose (hc t)
      have hp : z.val ∈ fiber m S p := fun t => Classical.choose_spec (hc t)
      exact Set.mem_iUnion.mpr ⟨⟨p, (hactual p).mpr ⟨z.val, hp⟩⟩, hp⟩
    have hUclopen (p : Set.range (sigma m S)) : IsClopen (U p) := by
      refine ⟨?_, hUopen p⟩
      rw [← isOpen_compl_iff]
      have he : (U p)ᶜ = ⋃ q : {q : Set.range (sigma m S) // q ≠ p}, U q.val := by
        ext z
        constructor
        · intro hz
          obtain ⟨q, hq⟩ := Set.mem_iUnion.mp (hUcover.symm ▸ Set.mem_univ z)
          exact Set.mem_iUnion.mpr ⟨⟨q, by intro he; exact hz (he ▸ hq)⟩, hq⟩
        · intro hz hp
          obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hz
          exact Set.disjoint_left.mp (hUdisj q.property) hq hp
      rw [he]
      exact isOpen_iUnion (fun q => hUopen q.val)
    have hUconn (p : Set.range (sigma m S)) : IsConnected (U p) := by
      have he : Subtype.val '' U p = fiber m S p.val :=
        Set.image_preimage_eq_of_subset (by simpa only [Subtype.range_coe] using hsubset p.val)
      refine ⟨?_, IsInducing.subtypeVal.isPreconnected_image.mp (by rw [he]; exact hconnected p.val)⟩
      obtain ⟨z, hz⟩ := (hactual p.val).mp p.property
      exact ⟨⟨z, hsubset p.val hz⟩, hz⟩
    exact (Nat.card_congr (ConnectedComponents.equivOfIsClopenOfIsConnected
      hUclopen hUdisj hUcover hUconn)).symm.trans hcomponents

end D5.S3.Arith.FibonacciAtomic.SparseWindowFiberGeometry
