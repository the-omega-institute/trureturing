/- GID: D5/S3/Arith/FibonacciAtomic/SparseWindowFiberGeometry
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SparseWindowFiberGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sparse window fibres are the components between translated circle cuts. -/

import D5.S1.Digit.Infinite.SparseWindowMutualDetermination
import D5.S1.Phase.Basic
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
open Set

local notation "Circle" => AddCircle (1 : ℝ)

/-- The points giving the specified window label at every retained time. -/
noncomputable def fiber (m : ℕ) (S : Finset ℕ) (p : (t : S) → X m) : Set Circle :=
  {z | ∀ t : S, z + goldenPhase (t.val : ℤ) ∈ A (p t)}

/-- The circle with all translated window cuts removed. -/
noncomputable def regularDomain (m : ℕ) (S : Finset ℕ) : Set Circle :=
  (E '' (↑(cuts m S) : Set ℕ))ᶜ

private theorem integer_of_equal_circle {x y : ℝ} (h : (x : Circle) = y) :
    ∃ k : ℤ, x - y = k := by
  have hz : ((x - y : ℝ) : Circle) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  exact ⟨k, by simpa only [zsmul_eq_mul, mul_one] using hk.symm⟩

private theorem short_lift_offset_eq {l u a b x y v w t : ℝ} {i j : ℤ}
    (hx : x ∈ Ioo l u) (hy : y ∈ Ioo l u)
    (hv : v ∈ Ioo a b) (hw : w ∈ Ioo a b)
    (hlen : u - l + (b - a) ≤ 1)
    (hi : x + t - v = i) (hj : y + t - w = j) : i = j := by
  have hsmall : (i : ℝ) - j < 1 ∧ (j : ℝ) - i < 1 := by
    constructor <;> linarith only [hx.1, hx.2, hy.1, hy.2, hv.1, hv.2,
      hw.1, hw.2, hlen, hi, hj]
  have hsmall' : i - j < (1 : ℤ) ∧ j - i < (1 : ℤ) := by
    exact_mod_cast hsmall
  omega

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
    obtain ⟨k, hk⟩ := integer_of_equal_circle hcx.symm
    obtain ⟨j, hj⟩ := integer_of_equal_circle hcy.symm
    have hkj : k = j := short_lift_offset_eq hx.1 hy.1 hxx hyy (hlen i) hk hj
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

private theorem arc_avoids_cuts (m : ℕ) (hm : 1 ≤ m) (p : X m) :
    Disjoint (A p) (B m) := by
  apply Set.disjoint_left.mpr
  rintro z hz ⟨k, hk, rfl⟩
  obtain ⟨i, j, hi, him, hj, hjm, hei, hej, hC⟩ :=
    (window_cylinder_partition.2.2 m hm).2.2.2.2.2.1 p
  have hends := window_cylinder_partition.2.1 k hk.1
  have hminus : P m (eMinus k) = p := by
    change eMinus k ∈ C p
    rw [hC]
    exact Or.inl (by
      change D5.S1.Digit.Infinite.MultiplierObstruction.phase (eMinus k) ∈ A p
      rw [(hends.2 _).mpr (Or.inl rfl)]
      exact hz)
  have hplus : P m (ePlus k) = p := by
    change ePlus k ∈ C p
    rw [hC]
    exact Or.inl (by
      change D5.S1.Digit.Infinite.MultiplierObstruction.phase (ePlus k) ∈ A p
      rw [(hends.2 _).mpr (Or.inr rfl)]
      exact hz)
  exact ((window_cylinder_partition.2.2 m hm).2.2.2.2.2.2 k hk.1).mpr hk.2
    (hminus.trans hplus.symm)

private theorem arc_cover (m : ℕ) (hm : 1 ≤ m) (z : Circle) (hz : z ∉ B m) :
    ∃ p : X m, z ∈ A p := by
  have hab : b = a + 1 := by
    have halpha : alpha ^ 2 + alpha = 1 := by
      unfold alpha
      rw [Real.inv_goldenRatio]
      nlinarith [Real.goldenConj_sq]
    dsimp [a, b]
    linarith
  have hcover : z ∈ (fun x : ℝ => (x : Circle)) '' Icc a b := by
    rw [hab, AddCircle.coe_image_Icc_eq]
    trivial
  obtain ⟨x, hx, rfl⟩ := hcover
  have hx' : x ∈ ⋃ p : X m, I p := by
    rw [(window_cylinder_partition.2.2 m hm).2.2.1]
    exact hx
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx'
  rw [((window_cylinder_partition.2.2 m hm).2.1 p).2.2.2.2.1] at hp
  refine ⟨p, x, ⟨?_, ?_⟩, rfl⟩
  · apply lt_of_le_of_ne hp.1
    intro he
    apply hz
    rw [← (window_cylinder_partition.2.2 m hm).2.2.2.2.1]
    exact ⟨p, Or.inl (congrArg (fun x : ℝ => (x : Circle)) he.symm)⟩
  · apply lt_of_le_of_ne hp.2
    intro he
    apply hz
    rw [← (window_cylinder_partition.2.2 m hm).2.2.2.2.1]
    exact ⟨p, Or.inr (congrArg (fun x : ℝ => (x : Circle)) he)⟩

private theorem arc_unique (m : ℕ) (hm : 1 ≤ m) (p q : X m) (z : Circle)
    (hp : z ∈ A p) (hq : z ∈ A q) : p = q := by
  have hab : b = a + 1 := by
    have halpha : alpha ^ 2 + alpha = 1 := by
      unfold alpha
      rw [Real.inv_goldenRatio]
      nlinarith [Real.goldenConj_sq]
    dsimp [a, b]
    linarith
  have hc : z ∈ (fun x : ℝ => (x : Circle)) '' Icc a b := by
    rw [hab, AddCircle.coe_image_Icc_eq]
    trivial
  obtain ⟨r, hr, rfl⟩ := hc
  obtain ⟨x, hx⟩ := (signed_series_range.1.symm ▸ hr : r ∈ Set.range signedValue)
  have hphase : D5.S1.Digit.Infinite.MultiplierObstruction.phase x = (r : Circle) :=
    congrArg (fun x : ℝ => (x : Circle)) hx
  have hxp : P m x = p := by
    change x ∈ C p
    obtain ⟨i, j, hi, him, hj, hjm, hei, hej, hC⟩ :=
      (window_cylinder_partition.2.2 m hm).2.2.2.2.2.1 p
    rw [hC]
    exact Or.inl (by change _ ∈ A p; rwa [hphase])
  have hxq : P m x = q := by
    change x ∈ C q
    obtain ⟨i, j, hi, him, hj, hjm, hei, hej, hC⟩ :=
      (window_cylinder_partition.2.2 m hm).2.2.2.2.2.1 q
    rw [hC]
    exact Or.inl (by change _ ∈ A q; rwa [hphase])
  exact hxp.symm.trans hxq

private theorem translated_cut (t j : ℕ) :
    E (t + j) + goldenPhase (t : ℤ) = E j := by
  simp only [E, goldenPhase, Nat.cast_add, Int.cast_natCast, ← AddCircle.coe_add]
  congr 1
  ring

private theorem regular_domain_iff (m : ℕ) (S : Finset ℕ) (z : Circle) :
    z ∈ regularDomain m S ↔ ∀ t : S, z + goldenPhase (t.val : ℤ) ∉ B m := by
  classical
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
  exact (QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo).preimage
    (continuous_id.add continuous_const)

private theorem phase_tail_dense (bound : ℕ) :
    DenseRange (fun n : ℕ => goldenPhase ((n + bound + 1 : ℕ) : ℤ)) := by
  have hz : DenseRange (fun n : ℤ => n • (Real.goldenRatio : Circle)) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using Real.goldenRatio_irrational)
  have hn : DenseRange (fun n : ℕ => n • (Real.goldenRatio : Circle)) :=
    denseRange_zsmul_iff_nsmul.mp hz
  let shift := Homeomorph.addRight ((bound + 1) • (Real.goldenRatio : Circle))
  have hd := shift.surjective.denseRange.comp hn shift.continuous
  convert hd using 1
  funext n
  simp only [goldenPhase, ← AddCircle.coe_nsmul, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  congr 1
  push_cast
  ring

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
      ∃ n : ℕ, bound < n ∧ goldenPhase (n : ℤ) ∈ fiber m S p) := by
  classical
  have hpos : 0 < alpha := inv_pos.mpr Real.goldenRatio_pos
  have hlt : alpha < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have halpha : alpha ^ 2 + alpha = 1 := by
    unfold alpha
    rw [Real.inv_goldenRatio]
    nlinarith [Real.goldenConj_sq]
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
    exact Set.disjoint_left.mp (arc_avoids_cuts m (by omega) (p t)) (hz t) hc
  have heq (p : (t : S) → X m) (z : Circle) (hz : z ∈ fiber m S p) :
      fiber m S p = connectedComponentIn (regularDomain m S) z := by
    apply Set.Subset.antisymm
    · exact (hconnected p).subset_connectedComponentIn hz (hsubset p)
    · intro w hw t
      let f : Circle → Circle := fun z => z + goldenPhase (t.val : ℤ)
      let U : Set Circle := f ⁻¹' A (p t)
      let V : Set Circle := ⋃ q : {q : X m // q ≠ p t}, f ⁻¹' A q.val
      have hU : IsOpen U :=
        (QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo).preimage
          (continuous_id.add continuous_const)
      have hV : IsOpen V := isOpen_iUnion (fun q =>
        (QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo).preimage
          (continuous_id.add continuous_const))
      have hdisjoint : Disjoint U V := by
        apply Set.disjoint_left.mpr
        intro x hx hVx
        obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hVx
        exact q.property (arc_unique m (by omega) q.val (p t) (f x) hq hx)
      have hcover : connectedComponentIn (regularDomain m S) z ⊆ U ∪ V := by
        intro x hx
        have hr := (regular_domain_iff m S x).mp
          (connectedComponentIn_subset (regularDomain m S) z hx) t
        obtain ⟨q, hq⟩ := arc_cover m (by omega) (f x) hr
        by_cases he : q = p t
        · apply Or.inl
          change f x ∈ A (p t)
          rwa [he] at hq
        · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨q, he⟩, hq⟩)
      exact IsPreconnected.subset_left_of_subset_union hU hV hdisjoint hcover
        ⟨z, mem_connectedComponentIn (hsubset p hz), hz t⟩
        isPreconnected_connectedComponentIn hw
  refine ⟨heq, ?_, ?_, ?_, ?_⟩
  · intro p q z w hz hw
    constructor
    · intro hsame
      have hw' : w ∈ fiber m S p := by
        rw [heq p z hz, hsame]
        exact mem_connectedComponentIn (hsubset q hw)
      funext t
      exact arc_unique m (by omega) (p t) (q t)
        (w + goldenPhase (t.val : ℤ)) (hw' t) (hw t)
    · intro hpq
      subst q
      exact (heq p z hz).symm.trans (heq p w hw)
  · intro z hz
    have hc (t : S) : ∃ p : X m, z + goldenPhase (t.val : ℤ) ∈ A p :=
      arc_cover m (by omega) _ ((regular_domain_iff m S z).mp hz t)
    refine ⟨fun t => Classical.choose (hc t), fun t => Classical.choose_spec (hc t), ?_⟩
    intro q hq
    funext t
    exact arc_unique m (by omega) (q t) (Classical.choose (hc t))
      (z + goldenPhase (t.val : ℤ)) (hq t) (Classical.choose_spec (hc t))
  · have hE : Function.Injective E := by
      intro i j hij
      have he : goldenPhase (-(i : ℤ)) = goldenPhase (-(j : ℤ)) := by
        simpa only [E, goldenPhase, Int.cast_neg, Int.cast_natCast] using hij
      exact_mod_cast neg_injective (goldenPhase_injective he)
    rw [Set.ncard_image_of_injective _ hE, Set.ncard_coe_finset]
  · intro p hp bound
    obtain ⟨n, hn⟩ := (phase_tail_dense bound).exists_mem_open (isOpen_fiber m S p) hp
    exact ⟨n + bound + 1, by omega, hn⟩

end D5.S3.Arith.FibonacciAtomic.SparseWindowFiberGeometry
