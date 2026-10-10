/- GID: D5/S1/Digit/Infinite/SparseWindowMutualDetermination
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SparseWindowMutualDetermination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sparse Fibonacci windows have equal fibres precisely when their cuts agree. -/
import D5.S1.Digit.Infinite.WindowCylinderPartition
import D5.S1.Phase.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic
set_option autoImplicit false
namespace D5.S1.Digit.Infinite.SparseWindowMutualDetermination
open D5.S1.Digit.Infinite.SuccessorContinuity
open D5.S1.Digit.Infinite.SignedSeriesRange
open D5.S1.Digit.Infinite.MultiplierObstruction
open D5.S1.Digit.Infinite.WindowSuccessorGraph
open D5.S1.Digit.Infinite.WindowCylinderPartition
open D5.S1.Digit
open scoped Topology
/-- The length-L window of the canonical natural Fibonacci row. -/
def q (L n : ℕ) : X L := P L (zRow n)
/-- Observations at the retained times of one natural source. -/
def sigma (m : ℕ) (S : Finset ℕ) (n : ℕ) : (t : S) → X m :=
  fun t => q m (n + t.val)
/-- The inclusive natural indices of all translated query cuts. -/
def cuts (m : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.biUnion (fun t => Finset.Icc (t + 1) (t + G m))
/-- The raw canonical digits of a natural source have its value and Boolean row. -/
theorem natural_row_raw_data (n : ℕ) : rawValue (rawOfZeckendorf (Nat.zeckendorf n)) = n ∧
    ∀ j : ℕ, (if (zRow n).val j then (1 : ℝ) else 0) =
      (rawOfZeckendorf (Nat.zeckendorf n) j : ℝ) := by
  classical
  let r := rawOfZeckendorf (Nat.zeckendorf n)
  have hr : CanonicalRaw r :=
    canonicalRaw_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf n)
  have hv : rawValue r = n := by
    rw [rawValue_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf n),
      Nat.sum_zeckendorf_fib]
  have hd (j : ℕ) : (if (zRow n).val j then (1 : ℝ) else 0) = r j := by
    have hm : (zRow n).val j = true ↔ r j ≠ 0 := by
      change decide (GoldenBase4AutomataOracle.zeckendorfBit n j = 1) = true ↔ _
      simp only [decide_eq_true_eq]
      have hb : GoldenBase4AutomataOracle.zeckendorfBit n j = 1 ↔
          j + 2 ∈ Nat.zeckendorf n := by
        by_cases h : j + 2 ∈ Nat.zeckendorf n <;>
          simp [GoldenBase4AutomataOracle.zeckendorfBit, D5.S0.Conventions.wdigits, h]
      rw [hb]
      rw [← rawToZeckendorf_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf n)]
      simp [rawToZeckendorf, Finsupp.mem_toMultiset, r]
    have hb := hr.1 j
    cases h : (zRow n).val j <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · have hz : r j = 0 := by simpa [h] using hm
      simp [hz]
    · have hn : r j = 1 := by have := hm.mp h; omega
      simp [hn]
  exact ⟨hv, hd⟩
/-- The phase of the canonical natural row is its golden rotation phase. -/
theorem natural_row_phase (n : ℕ) : phase (zRow n) =
    (((n : ℝ) * Real.goldenRatio : ℝ) : AddCircle (1 : ℝ)) := by
  classical
  let r := rawOfZeckendorf (Nat.zeckendorf n)
  have hv : rawValue r = n := (natural_row_raw_data n).1
  have hd (j : ℕ) : (if (zRow n).val j then (1 : ℝ) else 0) = r j :=
    (natural_row_raw_data n).2 j
  have hc (j : ℕ) : (-1 : ℝ) ^ (j + 1) * alpha ^ (j + 2) =
      (Nat.fib (j + 2) : ℝ) * Real.goldenRatio - Nat.fib (j + 3) := by
    have h := Real.fib_succ_sub_goldenRatio_mul_fib (j + 2)
    rw [show j + 2 + 1 = j + 3 by omega] at h
    have he : Real.goldenConj = -alpha := by
      unfold alpha
      linarith [Real.inv_goldenRatio]
    rw [he, neg_pow] at h
    rw [show j + 2 = (j + 1) + 1 by omega, pow_succ] at h
    nlinarith
  have hs : signedValue (zRow n) =
      (n : ℝ) * Real.goldenRatio -
        (∑ j ∈ r.support, r j * Nat.fib (j + 3) : ℕ) := by
    unfold signedValue
    simp_rw [hd, hc]
    rw [tsum_eq_sum (s := r.support)]
    · have hv' : (∑ j ∈ r.support, r j * Nat.fib (j + 2) : ℕ) = n := hv
      push_cast at hv' ⊢
      simp_rw [show ∀ j, ((Nat.fib (j + 2) : ℝ) * Real.goldenRatio -
          Nat.fib (j + 3)) * r j = (r j : ℝ) * Nat.fib (j + 2) *
          Real.goldenRatio - (r j : ℝ) * Nat.fib (j + 3) by intro j; ring]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      rw [show (∑ j ∈ r.support, (r j : ℝ) * Nat.fib (j + 2)) = n by
        exact_mod_cast hv']
    · intro j hj
      have hz : r j = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hj
      simp only [hz, Nat.cast_zero, mul_zero]
  change (signedValue (zRow n) : AddCircle (1 : ℝ)) = _
  rw [hs, AddCircle.coe_sub]
  have hz : (((∑ j ∈ r.support, r j * Nat.fib (j + 3) : ℕ) : ℝ) :
      AddCircle (1 : ℝ)) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨(∑ j ∈ r.support, r j * Nat.fib (j + 3) : ℕ), by simp⟩
  exact sub_eq_self.mpr hz
/-- Natural golden phases avoid all positive negative-index cuts. -/
theorem natural_phase_avoids_cut (n k : ℕ) (hk : 1 ≤ k) :
    (((n : ℝ) * Real.goldenRatio : ℝ) : AddCircle (1 : ℝ)) ≠ E k := by
  intro he
  have hz : (((n + k : ℕ) : ℝ) * Real.goldenRatio : AddCircle (1 : ℝ)) = 0 := by
    calc
      _ = ((n : ℝ) * Real.goldenRatio : AddCircle (1 : ℝ)) - E k := by
        simp only [E, Nat.cast_add]; congr 1; ring
      _ = 0 := sub_eq_zero.mpr he
  obtain ⟨i, hi⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  apply (Real.goldenRatio_irrational.natCast_mul (m := n + k) (by omega)).ne_int i
  simpa only [zsmul_eq_mul, mul_one] using hi.symm
/-- A natural window label is equivalent to membership in its open cylinder arc. -/
theorem natural_window_arc (L : ℕ) (hL : 1 ≤ L) (n : ℕ) (p : X L) :
    q L n = p ↔ phase (zRow n) ∈ A p := by
  have hData := window_cylinder_partition.2.2
  have hEnds := window_cylinder_partition.2.1
  have hRowAvoid (n k : ℕ) (hk : 1 ≤ k) : phase (zRow n) ≠ E k := by
    rw [natural_row_phase]
    exact natural_phase_avoids_cut n k hk
  have hEndpoint (k : ℕ) (hk : 1 ≤ k) :
      phase (eMinus k) = E k ∧ phase (ePlus k) = E k :=
    ⟨((hEnds k hk).2 _).mpr (by exact Or.inl rfl),
      ((hEnds k hk).2 _).mpr (by exact Or.inr rfl)⟩
  obtain ⟨i, j, hi, hiL, hj, hjL, hei, hej, hC⟩ := (hData L hL).2.2.2.2.2.1 p
  change zRow n ∈ C p ↔ _
  rw [hC]
  constructor
  · rintro (hn | hn)
    · exact hn
    · rcases hn with hn | hn
      · exact False.elim (hRowAvoid n i hi (congrArg phase hn |>.trans (hEndpoint i hi).2))
      · have he : zRow n = eMinus j := by simpa only [Set.mem_singleton_iff] using hn
        exact False.elim (hRowAvoid n j hj (congrArg phase he |>.trans (hEndpoint j hj).1))
  · exact Or.inl
local notation "gamma" => (fun t : ℕ => (((t : ℝ) * Real.goldenRatio : ℝ) : AddCircle (1 : ℝ)))
theorem cut_injective : Function.Injective E := by
  intro i j hij
  have he : D5.S1.Phase.goldenPhase (-(i : ℤ)) = D5.S1.Phase.goldenPhase (-(j : ℤ)) := by
    simpa only [E, D5.S1.Phase.goldenPhase, Int.cast_neg, Int.cast_natCast, neg_mul] using hij
  exact_mod_cast neg_injective (D5.S1.Phase.goldenPhase_injective he)
theorem natural_phase_visit (U : Set (AddCircle (1 : ℝ))) (hU : IsOpen U) (hne : U.Nonempty) (B : ℕ) :
    ∃ n : ℕ, B < n ∧ (((n : ℝ) * Real.goldenRatio : ℝ) : AddCircle (1 : ℝ)) ∈ U := by
  classical
  have hz : DenseRange (fun k : ℤ => k • (Real.goldenRatio : AddCircle (1 : ℝ))) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using Real.goldenRatio_irrational)
  have hn : DenseRange (fun k : ℕ => k • (Real.goldenRatio : AddCircle (1 : ℝ))) :=
    denseRange_zsmul_iff_nsmul.mp hz
  let shift := Homeomorph.addRight
    ((B + 1) • (Real.goldenRatio : AddCircle (1 : ℝ)))
  have hd : DenseRange (fun k : ℕ =>
      k • (Real.goldenRatio : AddCircle (1 : ℝ)) +
        (B + 1) • (Real.goldenRatio : AddCircle (1 : ℝ))) :=
    shift.surjective.denseRange.comp hn shift.continuous
  obtain ⟨k, hk⟩ := hd.exists_mem_open hU hne
  refine ⟨k + B + 1, by omega, ?_⟩
  convert hk using 1
  simp only [← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
    ← AddCircle.coe_add]
  congr 1
  ring
private theorem natural_phase_translate (n t : ℕ) : phase (zRow (n + t)) = phase (zRow n) +
    (((t : ℝ) * Real.goldenRatio : ℝ) : AddCircle (1 : ℝ)) := by
  simp only [natural_row_phase, Nat.cast_add, ← AddCircle.coe_add]
  congr 1
  ring
private theorem endpoint_phase (k : ℕ) (hk : 1 ≤ k) :
    phase (eMinus k) = E k ∧ phase (ePlus k) = E k :=
  ⟨((window_cylinder_partition.2.1 k hk).2 _).mpr (by exact Or.inl rfl),
    ((window_cylinder_partition.2.1 k hk).2 _).mpr (by exact Or.inr rfl)⟩
theorem window_arc_avoids_cut (L : ℕ) (hL : 1 ≤ L) (p : X L) (k : ℕ)
    (hk : 1 ≤ k) (hkL : k ≤ G L) : E k ∉ A p := by
  classical
  intro ha
  obtain ⟨i, j, hi, hiL, hj, hjL, hei, hej, hC⟩ := (window_cylinder_partition.2.2 L hL).2.2.2.2.2.1 p
  have hminus : P L (eMinus k) = p := by
    change eMinus k ∈ C p
    rw [hC]
    exact Or.inl (by change phase (eMinus k) ∈ A p; rwa [(endpoint_phase k hk).1])
  have hplus : P L (ePlus k) = p := by
    change ePlus k ∈ C p
    rw [hC]
    exact Or.inl (by change phase (ePlus k) ∈ A p; rwa [(endpoint_phase k hk).2])
  exact ((window_cylinder_partition.2.2 L hL).2.2.2.2.2.2 k hk).mpr hkL (hminus.trans hplus.symm)
theorem window_arc_isOpen (L : ℕ) (p : X L) : IsOpen (A p) :=
  QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
theorem golden_inverse_data : 0 < alpha ∧ alpha < 1 ∧ alpha ^ 2 + alpha = 1 := by
  refine ⟨inv_pos.mpr Real.goldenRatio_pos,
    inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio, ?_⟩
  unfold alpha
  rw [Real.inv_goldenRatio]
  nlinarith [Real.goldenConj_sq]
private theorem signed_interval_length : b = a + 1 := by dsimp [a, b]; linarith [golden_inverse_data.2.2]
theorem window_arc_cover (L : ℕ) (hL : 1 ≤ L) (z : AddCircle (1 : ℝ))
    (hz : z ∉ B L) : ∃ p : X L, z ∈ A p := by
  classical
  have hc : z ∈ ((fun x : ℝ => (x : AddCircle (1 : ℝ))) '' Set.Icc a b) := by
    rw [signed_interval_length, AddCircle.coe_image_Icc_eq]
    trivial
  obtain ⟨x, hx, rfl⟩ := hc
  have hu := (window_cylinder_partition.2.2 L hL).2.2.1
  have hxU : x ∈ ⋃ p : X L, I p := by rwa [hu]
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hxU
  have hIp := ((window_cylinder_partition.2.2 L hL).2.1 p).2.2.2.2.1
  rw [hIp] at hp
  obtain ⟨i, j, hi, hiL, hj, hjL, hei, hej, hC⟩ := (window_cylinder_partition.2.2 L hL).2.2.2.2.2.1 p
  refine ⟨p, x, ⟨?_, ?_⟩, rfl⟩
  · apply lt_of_le_of_ne hp.1
    intro he
    apply hz
    exact ⟨i, ⟨hi, hiL⟩, hei.symm.trans (congrArg (fun r : ℝ => (r : AddCircle (1 : ℝ))) he)⟩
  · apply lt_of_le_of_ne hp.2
    intro he
    apply hz
    exact ⟨j, ⟨hj, hjL⟩, hej.symm.trans (congrArg (fun r : ℝ => (r : AddCircle (1 : ℝ))) he.symm)⟩
private theorem window_cut_orientation (L : ℕ) (hL : 1 ≤ L) (k : ℕ) (hk : 1 ≤ k) (hkL : k ≤ G L) :
    ((upper (P L (eMinus k)) : ℝ) : AddCircle (1 : ℝ)) = E k ∧
    ((ell (P L (ePlus k)) : ℝ) : AddCircle (1 : ℝ)) = E k := by
  classical
  constructor
  · let p := P L (eMinus k)
    obtain ⟨i, j, hi, hiL, hj, hjL, hei, hej, hC⟩ := (window_cylinder_partition.2.2 L hL).2.2.2.2.2.1 p
    have hm : eMinus k ∈ C p := rfl
    rw [hC] at hm
    rcases hm with hm | hm
    · exact False.elim (window_arc_avoids_cut L hL p k hk hkL (by
        change phase (eMinus k) ∈ A p at hm; rwa [(endpoint_phase k hk).1] at hm))
    · rcases hm with hm | hm
      · have he : k = i := cut_injective ((endpoint_phase k hk).1.symm.trans
          ((congrArg phase hm).trans (endpoint_phase i hi).2))
        subst i
        exact False.elim ((window_cylinder_partition.2.1 k hk).1 hm)
      · have heq : eMinus k = eMinus j := by simpa only [Set.mem_singleton_iff] using hm
        have he : k = j := cut_injective ((endpoint_phase k hk).1.symm.trans
          ((congrArg phase heq).trans (endpoint_phase j hj).1))
        exact hej.trans (congrArg E he.symm)
  · let p := P L (ePlus k)
    obtain ⟨i, j, hi, hiL, hj, hjL, hei, hej, hC⟩ := (window_cylinder_partition.2.2 L hL).2.2.2.2.2.1 p
    have hm : ePlus k ∈ C p := rfl
    rw [hC] at hm
    rcases hm with hm | hm
    · exact False.elim (window_arc_avoids_cut L hL p k hk hkL (by
        change phase (ePlus k) ∈ A p at hm; rwa [(endpoint_phase k hk).2] at hm))
    · rcases hm with hm | hm
      · have he : k = i := cut_injective ((endpoint_phase k hk).2.symm.trans
          ((congrArg phase hm).trans (endpoint_phase i hi).2))
        exact hei.trans (congrArg E he.symm)
      · have heq : ePlus k = eMinus j := by simpa only [Set.mem_singleton_iff] using hm
        have he : k = j := cut_injective ((endpoint_phase k hk).2.symm.trans
          ((congrArg phase heq).trans (endpoint_phase j hj).1))
        subst j
        exact False.elim ((window_cylinder_partition.2.1 k hk).1 heq.symm)
theorem circle_integer_offset (x y : ℝ) (h : (x : AddCircle (1 : ℝ)) = y) :
    ∃ k : ℤ, (k : ℝ) = x - y := by
  have hz : ((x - y : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  simpa only [zsmul_eq_mul, mul_one] using (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
private theorem circle_integer_zero (k : ℤ) : ((k : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨k, by simp⟩
private theorem window_cut_collar (L : ℕ) (hL : 1 ≤ L) (k : ℕ) (hk : 1 ≤ k) (hkL : k ≤ G L) :
    ∃ c δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      (c : AddCircle (1 : ℝ)) = E k ∧
      (∀ x ∈ Set.Ioo (c - δ) c,
        (x : AddCircle (1 : ℝ)) ∈ A (P L (eMinus k))) ∧
      ∀ x ∈ Set.Ioo c (c + δ),
        (x : AddCircle (1 : ℝ)) ∈ A (P L (ePlus k)) := by
  classical
  let pm := P L (eMinus k)
  let pp := P L (ePlus k)
  let c := upper pm
  have hc : (c : AddCircle (1 : ℝ)) = E k := (window_cut_orientation L hL k hk hkL).1
  have he : (c : AddCircle (1 : ℝ)) = ell pp :=
    hc.trans (window_cut_orientation L hL k hk hkL).2.symm
  obtain ⟨z, hz⟩ := circle_integer_offset c (ell pp) he
  have hm : 0 < upper pm - ell pm := by
    rw [((window_cylinder_partition.2.2 L hL).2.1 pm).2.2.2.2.2.1]
    exact ((window_cylinder_partition.2.2 L hL).2.1 pm).2.2.2.2.2.2.1
  have hp : 0 < upper pp - ell pp := by
    rw [((window_cylinder_partition.2.2 L hL).2.1 pp).2.2.2.2.2.1]
    exact ((window_cylinder_partition.2.2 L hL).2.1 pp).2.2.2.2.2.2.1
  let δ := min (min (upper pm - ell pm) (upper pp - ell pp)) (1 / 2) / 2
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hdm : δ < upper pm - ell pm := by
    have := min_le_left (min (upper pm - ell pm) (upper pp - ell pp)) (1 / 2)
    have := min_le_left (upper pm - ell pm) (upper pp - ell pp)
    dsimp [δ]; linarith
  have hdp : δ < upper pp - ell pp := by
    have := min_le_left (min (upper pm - ell pm) (upper pp - ell pp)) (1 / 2)
    have := min_le_right (upper pm - ell pm) (upper pp - ell pp)
    dsimp [δ]; linarith
  refine ⟨c, δ, hd, ?_, hc, ?_, ?_⟩
  · have := min_le_right (min (upper pm - ell pm) (upper pp - ell pp)) (1 / 2)
    dsimp [δ]; linarith
  · intro x hx
    exact ⟨x, ⟨by dsimp [c] at hx; linarith [hx.1], hx.2⟩, rfl⟩
  · intro x hx
    refine ⟨x - z, ⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
    simp only [AddCircle.coe_sub, circle_integer_zero, sub_zero]
private theorem natural_phase_visit_sides (c δ : ℝ) (hd : 0 < δ) (hdhalf : δ < 1 / 2) (U : Set (AddCircle (1 : ℝ)))
    (hU : IsOpen U) (hcU : (c : AddCircle (1 : ℝ)) ∈ U) (B0 : ℕ) :
    ∃ a b : ℕ, B0 < a ∧ B0 < b ∧
      (∃ x ∈ Set.Ioo (c - δ) c, phase (zRow a) = (x : AddCircle (1 : ℝ))) ∧
      (∃ y ∈ Set.Ioo c (c + δ), phase (zRow b) = (y : AddCircle (1 : ℝ))) ∧
      phase (zRow a) ∈ U ∧ phase (zRow b) ∈ U := by
  classical
  have hopen : IsOpen ((fun x : ℝ => (x : AddCircle (1 : ℝ))) ⁻¹' U) :=
    hU.preimage (AddCircle.continuous_mk' (1 : ℝ))
  obtain ⟨lo, hi, hci, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hopen.mem_nhds hcU)
  have hlo : lo < c := hci.1
  have hhi : c < hi := hci.2
  let ε := min δ (min (c - lo) (hi - c)) / 2
  have he : 0 < ε := by dsimp [ε]; positivity
  have hed : ε < δ := by
    have := min_le_left δ (min (c - lo) (hi - c)); dsimp [ε]; linarith
  have hel : ε < c - lo := by
    have := min_le_right δ (min (c - lo) (hi - c))
    have := min_le_left (c - lo) (hi - c); dsimp [ε]; linarith
  have heh : ε < hi - c := by
    have := min_le_right δ (min (c - lo) (hi - c))
    have := min_le_right (c - lo) (hi - c); dsimp [ε]; linarith
  let Uminus := (fun x : ℝ => (x : AddCircle (1 : ℝ))) '' Set.Ioo (c - ε) c
  let Uplus := (fun x : ℝ => (x : AddCircle (1 : ℝ))) '' Set.Ioo c (c + ε)
  let chart := AddCircle.openPartialHomeomorphCoe (1 : ℝ) (c - 1 / 2)
  have hmchart : Set.Ioo (c - ε) c ⊆ chart.source := by
    intro x hx
    change x ∈ Set.Ioo (c - 1 / 2) (c - 1 / 2 + 1)
    constructor <;> linarith only [hx.1, hx.2, hed, hdhalf]
  have hpchart : Set.Ioo c (c + ε) ⊆ chart.source := by
    intro x hx
    change x ∈ Set.Ioo (c - 1 / 2) (c - 1 / 2 + 1)
    constructor <;> linarith only [hx.1, hx.2, hed, hdhalf]
  have hom : IsOpen Uminus := chart.isOpen_image_of_subset_source isOpen_Ioo hmchart
  have hop : IsOpen Uplus := chart.isOpen_image_of_subset_source isOpen_Ioo hpchart
  have hnm : Uminus.Nonempty := Set.Nonempty.image _ (Set.nonempty_Ioo.mpr (by linarith))
  have hnp : Uplus.Nonempty := Set.Nonempty.image _ (Set.nonempty_Ioo.mpr (by linarith))
  obtain ⟨a, ha, xa, hxa, hea⟩ := natural_phase_visit Uminus hom hnm B0
  obtain ⟨b, hb, xb, hxb, heb⟩ := natural_phase_visit Uplus hop hnp B0
  refine ⟨a, b, ha, hb, ⟨xa, ⟨by linarith [hxa.1], hxa.2⟩, ?_⟩,
    ⟨xb, ⟨hxb.1, by linarith [hxb.2]⟩, ?_⟩, ?_, ?_⟩
  · exact (natural_row_phase a).trans hea.symm
  · exact (natural_row_phase b).trans heb.symm
  · rw [natural_row_phase a, ← hea]
    exact hsub ⟨by linarith [hxa.1], by linarith [hxa.2]⟩
  · rw [natural_row_phase b, ← heb]
    exact hsub ⟨by linarith [hxb.1], by linarith [hxb.2]⟩
theorem translated_cut (t j : ℕ) : E (t + j) + gamma t = E j := by
  dsimp [E]
  rw [← AddCircle.coe_add]
  congr 1
  push_cast
  ring
private theorem translated_cut_mem (L t k : ℕ) : E k + gamma t ∈ B L ↔
    k ∈ Finset.Icc (t + 1) (t + G L) := by
  classical
  constructor
  · rintro ⟨j, ⟨hj1, hj2⟩, he⟩
    have he' : E (t + j) = E k := add_right_cancel
      ((translated_cut t j).trans he)
    have hk := cut_injective he'
    simp only [Finset.mem_Icc]
    omega
  · intro hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨k - t, ⟨by omega, by omega⟩, ?_⟩
    rw [← translated_cut t (k - t), show t + (k - t) = k by omega]
theorem phase_surjective : Function.Surjective phase := by
  intro z
  have hz : z ∈ ((fun r : ℝ => (r : AddCircle (1 : ℝ))) '' Set.Icc a b) := by
    rw [signed_interval_length, AddCircle.coe_image_Icc_eq]
    trivial
  obtain ⟨r, hr, rfl⟩ := hz
  have hr' : r ∈ Set.range signedValue := signed_series_range.1.symm ▸ hr
  obtain ⟨x, hx⟩ := hr'
  exact ⟨x, congrArg (fun r : ℝ => (r : AddCircle (1 : ℝ))) hx⟩
theorem window_arc_unique (L : ℕ) (hL : 1 ≤ L) (p q : X L) (z : AddCircle (1 : ℝ))
    (hp : z ∈ A p) (hq : z ∈ A q) : p = q := by
  obtain ⟨x, rfl⟩ := phase_surjective z
  obtain ⟨i, j, hi, hiL, hj, hjL, hei, hej, hCp⟩ := (window_cylinder_partition.2.2 L hL).2.2.2.2.2.1 p
  obtain ⟨i', j', hi', hiL', hj', hjL', hei', hej', hCq⟩ := (window_cylinder_partition.2.2 L hL).2.2.2.2.2.1 q
  have hxp : P L x = p := by change x ∈ C p; rw [hCp]; exact Or.inl hp
  have hxq : P L x = q := by change x ∈ C q; rw [hCq]; exact Or.inl hq
  exact hxp.symm.trans hxq
theorem missing_cut_witness (m M : ℕ) (hm : 1 ≤ m)
    (hmM : m ≤ M) (S : Finset ℕ) (k : ℕ) (hk : k ∈ Finset.Icc 1 (G M)) (hnot : k ∉ cuts m S)
    (B0 : ℕ) : ∃ a b : ℕ, B0 < a ∧ B0 < b ∧
      sigma m S a = sigma m S b ∧ q M a ≠ q M b := by
  classical
  have hM : 1 ≤ M := by omega
  have hkm : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkM : k ≤ G M := (Finset.mem_Icc.mp hk).2
  have hnc (t : S) : E k + gamma t.val ∉ B m := by
    intro hc
    apply hnot
    exact Finset.mem_biUnion.mpr ⟨t.val, t.property, (translated_cut_mem m t.val k).mp hc⟩
  let ps (t : S) := Classical.choose (window_arc_cover m hm (E k + gamma t.val) (hnc t))
  have hps (t : S) : E k + gamma t.val ∈ A (ps t) :=
    Classical.choose_spec (window_arc_cover m hm (E k + gamma t.val) (hnc t))
  let U : Set (AddCircle (1 : ℝ)) := ⋂ t : S,
    (fun z => z + gamma t.val) ⁻¹' A (ps t)
  have hU : IsOpen U := isOpen_iInter_of_finite (fun t =>
    (window_arc_isOpen m (ps t)).preimage (continuous_id.add continuous_const))
  have hkU : E k ∈ U := Set.mem_iInter.mpr hps
  obtain ⟨c, δ, hd, hdhalf, hc, hleft, hright⟩ := window_cut_collar M hM k hkm hkM
  obtain ⟨a, b, ha, hb, ⟨x, hx, hxa⟩, ⟨y, hy, hyb⟩, haU, hbU⟩ :=
    natural_phase_visit_sides c δ hd hdhalf U hU (hc.symm ▸ hkU) B0
  have hqa : q M a = P M (eMinus k) := (natural_window_arc M hM a _).mpr
    (hxa.symm ▸ hleft x hx)
  have hqb : q M b = P M (ePlus k) := (natural_window_arc M hM b _).mpr
    (hyb.symm ▸ hright y hy)
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · funext t
    have hpa : q m (a + t.val) = ps t := (natural_window_arc m hm (a + t.val) _).mpr (by
      rw [natural_phase_translate]
      exact Set.mem_iInter.mp haU t)
    have hpb : q m (b + t.val) = ps t := (natural_window_arc m hm (b + t.val) _).mpr (by
      rw [natural_phase_translate]
      exact Set.mem_iInter.mp hbU t)
    exact hpa.trans hpb.symm
  · rw [hqa, hqb]
    exact ((window_cylinder_partition.2.2 M hM).2.2.2.2.2.2 k hkm).mpr hkM
theorem extra_cut_witness (m M : ℕ) (hm : 1 ≤ m)
    (hmM : m ≤ M) (S : Finset ℕ) (k : ℕ) (hk : k ∈ cuts m S) (hnot : k ∉ Finset.Icc 1 (G M))
    (B0 : ℕ) : ∃ a b : ℕ, B0 < a ∧ B0 < b ∧
      q M a = q M b ∧ sigma m S a ≠ sigma m S b := by
  classical
  have hM : 1 ≤ M := by omega
  obtain ⟨t, ht, hkt⟩ := Finset.mem_biUnion.mp hk
  have hkj : 1 ≤ k - t ∧ k - t ≤ G m := by
    simp only [Finset.mem_Icc] at hkt
    omega
  have hknc : E k ∉ B M := by
    rintro ⟨j, hj, he⟩
    have hke : j = k := cut_injective he
    apply hnot
    have hb : 1 ≤ j ∧ j ≤ G M := hj
    rw [hke] at hb
    exact Finset.mem_Icc.mpr hb
  obtain ⟨p, hp⟩ := window_arc_cover M hM (E k) hknc
  obtain ⟨c, δ, hd, hdhalf, hc, hleft, hright⟩ := window_cut_collar m hm (k - t) hkj.1 hkj.2
  let c0 := c - (t : ℝ) * Real.goldenRatio
  have hc0 : (c0 : AddCircle (1 : ℝ)) = E k := by
    have he : E k + gamma t = E (k - t) := by
      simpa only [show t + (k - t) = k by
        have := (Finset.mem_Icc.mp hkt).1; omega] using translated_cut t (k - t)
    dsimp [c0]
    rw [hc]
    exact (eq_sub_iff_add_eq.mpr he).symm
  obtain ⟨a, b, ha, hb, ⟨x, hx, hxa⟩, ⟨y, hy, hyb⟩, hap, hbp⟩ :=
    natural_phase_visit_sides c0 δ hd hdhalf (A p) (window_arc_isOpen M p) (hc0.symm ▸ hp) B0
  have hqa : q M a = p := (natural_window_arc M hM a p).mpr hap
  have hqb : q M b = p := (natural_window_arc M hM b p).mpr hbp
  have hma : q m (a + t) = P m (eMinus (k - t)) := (natural_window_arc m hm (a + t) _).mpr (by
    rw [natural_phase_translate, hxa]
    exact hleft (x + (t : ℝ) * Real.goldenRatio) (by
      dsimp [c0] at hx
      constructor <;> linarith [hx.1, hx.2]))
  have hmb : q m (b + t) = P m (ePlus (k - t)) := (natural_window_arc m hm (b + t) _).mpr (by
    rw [natural_phase_translate, hyb]
    exact hright (y + (t : ℝ) * Real.goldenRatio) (by
      dsimp [c0] at hy
      constructor <;> linarith [hy.1, hy.2]))
  refine ⟨a, b, ha, hb, hqa.trans hqb.symm, ?_⟩
  intro hs
  have he := congrFun hs ⟨t, ht⟩
  change q m (a + t) = q m (b + t) at he
  rw [hma, hmb] at he
  exact ((window_cylinder_partition.2.2 m hm).2.2.2.2.2.2 (k - t) hkj.1).mpr hkj.2 he
set_option maxHeartbeats 1600000 in
-- The collar, common-lift, and binary-anchor arguments form one joint geometry proof.
/-- Equal translated cut sets characterize equal natural fibres. The actual-image
equivalence uses the canonical finite value V in its forward map. -/
theorem sparse_window_mutual_determination (m M : ℕ) (hm : 1 ≤ m)
    (hmM : m ≤ M) (S : Finset ℕ) :
    ((∀ a b : ℕ, q M a = q M b ↔ sigma m S a = sigma m S b) ↔
      cuts m S = Finset.Icc 1 (G M)) ∧
    (cuts m S = Finset.Icc 1 (G M) →
      Nat.card (Set.range (q M)) = G M ∧
      Nat.card (Set.range (sigma m S)) = G M ∧
      ∃ e : X M ≃ Set.range (sigma m S),
        (∀ p, (e p).val = sigma m S (V p)) ∧
        (∀ n, (e (q M n)).val = sigma m S n) ∧
        ∀ n, e.symm ⟨sigma m S n, ⟨n, rfl⟩⟩ = q M n) := by
  classical
  have hRawRow := natural_row_raw_data
  have hPhase := natural_row_phase
  have hAvoid := natural_phase_avoids_cut
  -- Canonical re-encoding realizes every legal finite word by its displayed value.
  have hqV (L : ℕ) (p : X L) : q L (V p) = p := by
    classical
    let r : RawDigits := Finsupp.onFinset (Finset.range L)
      (fun j => if h : j < L then if p.val ⟨j, h⟩ then 1 else 0 else 0)
      (by intro j hj; by_contra hn; simp [Finset.mem_range.not.mp hn] at hj)
    have hc : CanonicalRaw r := by
      constructor
      · intro j; dsimp [r]; split <;> (try split) <;> omega
      · intro j hj
        by_cases h : j + 1 < L
        · have hjL : j < L := by omega
          have htrue : p.val ⟨j, hjL⟩ = true := by
            simpa [r, hjL] using hj
          have hn : p.val ⟨j + 1, h⟩ = false := by
            cases he : p.val ⟨j + 1, h⟩
            · rfl
            · exact False.elim (p.property j h ⟨htrue, he⟩)
          simp [r, h, hn]
        · simp [r, h]
    have hv : rawValue r = V p := by
      unfold rawValue V
      rw [Finset.sum_fin_eq_sum_range]
      dsimp [r]
      rw [Finsupp.sum_onFinset _ _ _ _ (by intros; simp)]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range.mp hj, ↓reduceDIte, D5.S0.Conventions.wValue]
      split <;> simp_all
    apply Subtype.ext
    funext j
    have he := rawToZeckendorf_eq_zeckendorf hc
    rw [hv] at he
    change decide (GoldenBase4AutomataOracle.zeckendorfBit (V p) j.val = 1) = p.val j
    apply Bool.eq_iff_iff.mpr
    simp [GoldenBase4AutomataOracle.zeckendorfBit, D5.S0.Conventions.wdigits,
      ← he, rawToZeckendorf, Finsupp.mem_toMultiset, r, j.isLt]
  have hData := window_cylinder_partition.2.2
  have hRowAvoid (n k : ℕ) (hk : 1 ≤ k) : phase (zRow n) ≠ E k := by
    rw [hPhase]
    exact hAvoid n k hk
  have hArc := natural_window_arc
  have hNecessary (hf : ∀ a b : ℕ, q M a = q M b ↔ sigma m S a = sigma m S b) :
      cuts m S = Finset.Icc 1 (G M) := by
    apply Finset.Subset.antisymm
    · intro k hk
      by_contra hn
      obtain ⟨a, b, ha, hb, hq, hs⟩ := extra_cut_witness m M hm hmM S k hk hn 0
      exact hs ((hf a b).mp hq)
    · intro k hk
      by_contra hn
      obtain ⟨a, b, ha, hb, hs, hq⟩ := missing_cut_witness m M hm hmM S k hk hn 0
      exact hq ((hf a b).mpr hs)
  have hRowInterior (L : ℕ) (hL : 1 ≤ L) (n : ℕ) :
      signedValue (zRow n) ∈ Set.Ioo (ell (q L n)) (upper (q L n)) := by
    let p := q L n
    have hc : zRow n ∈ C p := rfl
    have hi : signedValue (zRow n) ∈ I p := by
      rw [← ((hData L hL).2.1 p).2.2.2.1]
      exact Set.mem_image_of_mem _ hc
    rw [((hData L hL).2.1 p).2.2.2.2.1] at hi
    obtain ⟨i, j, hi1, hiL, hj1, hjL, hei, hej, hC⟩ := (hData L hL).2.2.2.2.2.1 p
    constructor
    · apply lt_of_le_of_ne hi.1
      intro he
      apply hRowAvoid n i hi1
      exact (congrArg (fun x : ℝ => (x : AddCircle (1 : ℝ))) he.symm).trans hei
    · apply lt_of_le_of_ne hi.2
      intro he
      apply hRowAvoid n j hj1
      exact (congrArg (fun x : ℝ => (x : AddCircle (1 : ℝ))) he).trans hej
  have hWidth (L : ℕ) (hL : 1 ≤ L) (p : X L) :
      upper p - ell p ≤ alpha ∧
        (2 ≤ L → upper p - ell p ≤ alpha ^ 2) := by
    rw [((hData L hL).2.1 p).2.2.2.2.2.1]
    constructor
    · simpa only [pow_one] using pow_le_pow_of_le_one golden_inverse_data.1.le golden_inverse_data.2.1.le
        (show 1 ≤ d p by dsimp [d]; omega)
    · intro hL2
      exact pow_le_pow_of_le_one golden_inverse_data.1.le golden_inverse_data.2.1.le
        (show 2 ≤ d p by dsimp [d]; omega)
  have hShortLift (x y l u a b t : ℝ)
      (hx : x ∈ Set.Ioo l u) (hy : y ∈ Set.Ioo l u)
      (hw : u - l + (b - a) ≤ 1)
      (hxa : ((x + t : ℝ) : AddCircle (1 : ℝ)) ∈
        (fun s : ℝ => (s : AddCircle (1 : ℝ))) '' Set.Ioo a b)
      (hya : ((y + t : ℝ) : AddCircle (1 : ℝ)) ∈
        (fun s : ℝ => (s : AddCircle (1 : ℝ))) '' Set.Ioo a b) :
      ∃ k : ℤ, x + t - k ∈ Set.Ioo a b ∧ y + t - k ∈ Set.Ioo a b := by
    obtain ⟨xa, hxa, hea⟩ := hxa
    obtain ⟨ya, hya, heb⟩ := hya
    obtain ⟨i, hi⟩ := circle_integer_offset (x + t) xa hea.symm
    obtain ⟨j, hj⟩ := circle_integer_offset (y + t) ya heb.symm
    have he : i = j := by
      rcases lt_trichotomy i j with hij | hij | hij
      · have hgap : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
        linarith only [hx.1, hx.2, hy.1, hy.2, hxa.1, hxa.2, hya.1, hya.2, hw, hi, hj, hgap]
      · exact hij
      · have hgap : (j : ℝ) + 1 ≤ i := by exact_mod_cast (show j + 1 ≤ i by omega)
        linarith only [hx.1, hx.2, hy.1, hy.2, hxa.1, hxa.2, hya.1, hya.2, hw, hi, hj, hgap]
    subst j
    refine ⟨i, ?_, ?_⟩
    · constructor <;> linarith only [hi, hxa.1, hxa.2]
    · constructor <;> linarith only [hj, hya.1, hya.2]
  have hPhi : Real.goldenRatio = 1 + alpha := by
    unfold alpha
    linarith [Real.inv_goldenRatio, Real.goldenRatio_add_goldenConj]
  have hCube : alpha ^ 3 = 2 * alpha - 1 := by
    nlinarith [golden_inverse_data.2.2, congrArg (fun x : ℝ => alpha * x) golden_inverse_data.2.2]
  have hBetaBounds : 1 / 3 < alpha ^ 2 ∧ alpha ^ 2 < 1 / 2 := by
    have hlow : 1 / 2 < alpha := by nlinarith [golden_inverse_data.1, golden_inverse_data.2.1, golden_inverse_data.2.2]
    have hhigh : alpha < 2 / 3 := by nlinarith [golden_inverse_data.1, golden_inverse_data.2.1, golden_inverse_data.2.2]
    constructor <;> nlinarith [golden_inverse_data.2.2]
  have hBinaryEnds (p : X 1) :
      (p.val 0 = false → ell p = -(alpha ^ 3) ∧ upper p = alpha ^ 2) ∧
      (p.val 0 = true → ell p = -alpha ∧ upper p = -(alpha ^ 3)) := by
    have hSp : Sp p = -alpha ^ 2 * (if p.val 0 then 1 else 0) := by
      simp [Sp]
    have hd : d p = 1 + if p.val 0 then 1 else 0 := by
      simp [d, List.ofFn_succ]
    have hsum : alpha ^ 2 + alpha ^ 3 = alpha := by nlinarith [golden_inverse_data.2.2, hCube]
    have hfour : alpha ^ 4 + alpha ^ 3 = alpha ^ 2 := by
      nlinarith [congrArg (fun x : ℝ => alpha ^ 2 * x) golden_inverse_data.2.2]
    constructor
    · intro hp
      simp only [ell, upper, hSp, hd, hp, Bool.false_eq_true, ↓reduceIte,
        mul_zero, zero_add, add_zero, pow_one, SignedSeriesFibres.r, a, b]
      constructor
      · rw [min_eq_right (by nlinarith [golden_inverse_data.1])]; ring
      · rw [max_eq_left (by nlinarith [golden_inverse_data.1])]; ring
    · intro hp
      simp only [ell, upper, hSp, hd, hp, ↓reduceIte, mul_one,
        SignedSeriesFibres.r, a, b]
      have h1 : -alpha ^ 2 + (-alpha) ^ (1 + 1) * -alpha = -alpha := by
        calc
          _ = -alpha ^ 2 - alpha ^ 3 := by ring
          _ = -alpha := by linarith only [hsum]
      have h2 : -alpha ^ 2 + (-alpha) ^ (1 + 1) * alpha ^ 2 = -alpha ^ 3 := by
        calc
          _ = -alpha ^ 2 + alpha ^ 4 := by ring
          _ = -alpha ^ 3 := by linarith only [hfour]
      rw [h1, h2]
      constructor
      · exact min_eq_left (by nlinarith [golden_inverse_data.1])
      · exact max_eq_right (by nlinarith [golden_inverse_data.1])
  have hZeroSchedule (heq : cuts m S = Finset.Icc 1 (G M)) : 0 ∈ S := by
    have hG : 1 ≤ G M := by
      exact Nat.fib_pos.mpr (by omega)
    have h1 : 1 ∈ cuts m S := heq.symm ▸ Finset.mem_Icc.mpr ⟨le_rfl, hG⟩
    obtain ⟨t, ht, hti⟩ := Finset.mem_biUnion.mp h1
    have ht0 : t = 0 := by have := (Finset.mem_Icc.mp hti).1; omega
    simpa only [ht0] using ht
  have hBinaryPair (heq : cuts 1 S = Finset.Icc 1 (G M)) (hM : 2 ≤ M) :
      1 ∈ S ∨ 2 ∈ S := by
    have hG : 3 ≤ G M := by
      change Nat.fib 4 ≤ Nat.fib (M + 2)
      exact Nat.fib_mono (by omega)
    have h3 : 3 ∈ cuts 1 S := heq.symm ▸ Finset.mem_Icc.mpr ⟨by omega, hG⟩
    obtain ⟨t, ht, hti⟩ := Finset.mem_biUnion.mp h3
    have hg : G 1 = 2 := rfl
    simp only [Finset.mem_Icc, hg] at hti
    rcases (show t = 1 ∨ t = 2 by omega) with rfl | rfl
    · exact Or.inl ht
    · exact Or.inr ht
  have hBinaryZero (n t : ℕ) (ht : t = 1 ∨ t = 2)
      (h0 : (q 1 n).val 0 = false) (ht0 : (q 1 (n + t)).val 0 = false) :
      signedValue (zRow n) ∈
        if t = 1 then Set.Ioo (alpha ^ 2 - alpha ^ 3) (alpha ^ 2)
        else Set.Ioo (-(alpha ^ 3)) (alpha ^ 2 - alpha ^ 3) := by
    have hx := hRowInterior 1 (by omega) n
    have hy := hRowInterior 1 (by omega) (n + t)
    rw [(hBinaryEnds (q 1 n)).1 h0 |>.1,
      (hBinaryEnds (q 1 n)).1 h0 |>.2] at hx
    rw [(hBinaryEnds (q 1 (n + t))).1 ht0 |>.1,
      (hBinaryEnds (q 1 (n + t))).1 ht0 |>.2] at hy
    have he : ((signedValue (zRow n) + (t : ℝ) * Real.goldenRatio : ℝ) :
        AddCircle (1 : ℝ)) = signedValue (zRow (n + t)) := by
      rw [AddCircle.coe_add]
      exact (natural_phase_translate n t).symm
    obtain ⟨k, hk⟩ := circle_integer_offset _ _ he
    have hxr : -(alpha ^ 3) < signedValue (zRow n) := hx.1
    have hxu : signedValue (zRow n) < alpha ^ 2 := hx.2
    have hyr : -(alpha ^ 3) < signedValue (zRow (n + t)) := hy.1
    have hyu : signedValue (zRow (n + t)) < alpha ^ 2 := hy.2
    rw [hPhi] at hk
    rcases ht with rfl | rfl
    · simp only [Nat.cast_one, one_mul] at hk
      have hk1 : (1 : ℝ) < k := by linarith only [hk, hxr, hyu, hCube, golden_inverse_data.2.2]
      have hk3 : (k : ℝ) < 3 := by linarith only [hk, hxu, hyr, hCube, golden_inverse_data.2.2, golden_inverse_data.2.1]
      have hkI1 : (1 : ℤ) < k := by exact_mod_cast hk1
      have hkI3 : k < (3 : ℤ) := by exact_mod_cast hk3
      have hk2 : k = 2 := by omega
      simp only [hk2, Int.cast_ofNat] at hk
      simp only [↓reduceIte]
      constructor
      · linarith only [hk, hyr, golden_inverse_data.2.2]
      · exact hxu
    · norm_num only [Nat.cast_ofNat] at hk
      have hk2 : (2 : ℝ) < k := by linarith only [hk, hxr, hyu, hCube, golden_inverse_data.2.2, golden_inverse_data.1]
      have hk4 : (k : ℝ) < 4 := by linarith only [hk, hxu, hyr, hCube, golden_inverse_data.2.2, hBetaBounds.1]
      have hkI2 : (2 : ℤ) < k := by exact_mod_cast hk2
      have hkI4 : k < (4 : ℤ) := by exact_mod_cast hk4
      have hk3 : k = 3 := by omega
      simp only [hk3, Int.cast_ofNat] at hk
      simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
      constructor
      · exact hxr
      · linarith only [hk, hyu, hCube]
  have hAnchor (heq : cuts m S = Finset.Icc 1 (G M)) (hM2 : 2 ≤ M)
      (a b : ℕ) (hs : sigma m S a = sigma m S b) :
      ∃ l u : ℝ, signedValue (zRow a) ∈ Set.Ioo l u ∧
        signedValue (zRow b) ∈ Set.Ioo l u ∧ u - l ≤ alpha ^ 2 := by
    have h0 := hZeroSchedule heq
    have hs0 : q m a = q m b := by
      simpa only [sigma, Nat.add_zero] using congrFun hs ⟨0, h0⟩
    have hxa := hRowInterior m hm a
    have hxb := hRowInterior m hm b
    rw [← hs0] at hxb
    by_cases hm2 : 2 ≤ m
    · exact ⟨ell (q m a), upper (q m a), hxa, hxb, (hWidth m hm _).2 hm2⟩
    · have hm1 : m = 1 := by omega
      subst m
      have hpair : ∃ t : ℕ, t ∈ S ∧ (t = 1 ∨ t = 2) := by
        rcases hBinaryPair heq hM2 with ht | ht
        · exact ⟨1, ht, Or.inl rfl⟩
        · exact ⟨2, ht, Or.inr rfl⟩
      obtain ⟨t, ht, htpair⟩ := hpair
      have hst : q 1 (a + t) = q 1 (b + t) := congrFun hs ⟨t, ht⟩
      by_cases h0a : (q 1 a).val 0 = true
      · refine ⟨ell (q 1 a), upper (q 1 a), hxa, hxb, ?_⟩
        rw [(hBinaryEnds (q 1 a)).2 h0a |>.1, (hBinaryEnds (q 1 a)).2 h0a |>.2]
        linarith only [hCube, golden_inverse_data.2.2]
      · have hz0a : (q 1 a).val 0 = false := Bool.eq_false_iff.mpr h0a
        have hz0b : (q 1 b).val 0 = false := by rw [← hs0]; exact hz0a
        by_cases hta : (q 1 (a + t)).val 0 = true
        · let p := q 1 (a + t)
          have haA : ((signedValue (zRow a) + (t : ℝ) * Real.goldenRatio : ℝ) :
              AddCircle (1 : ℝ)) ∈ A p := by
            rw [AddCircle.coe_add]
            exact (natural_phase_translate a t) ▸ (hArc 1 (by omega) (a + t) p).mp rfl
          have hbA : ((signedValue (zRow b) + (t : ℝ) * Real.goldenRatio : ℝ) :
              AddCircle (1 : ℝ)) ∈ A p := by
            rw [AddCircle.coe_add]
            exact (natural_phase_translate b t) ▸ (hArc 1 (by omega) (b + t) p).mp hst.symm
          have hpwidth : upper p - ell p = alpha ^ 2 := by
            rw [(hBinaryEnds p).2 hta |>.1, (hBinaryEnds p).2 hta |>.2]
            linarith only [hCube, golden_inverse_data.2.2]
          have hwidth : upper (q 1 a) - ell (q 1 a) + (upper p - ell p) ≤ 1 := by
            linarith only [(hWidth 1 (by omega) (q 1 a)).1, hpwidth, golden_inverse_data.2.2]
          obtain ⟨k, hka, hkb⟩ := hShortLift _ _ (ell (q 1 a)) (upper (q 1 a))
            (ell p) (upper p) ((t : ℝ) * Real.goldenRatio) hxa hxb hwidth haA hbA
          refine ⟨ell p - (t : ℝ) * Real.goldenRatio + k,
            upper p - (t : ℝ) * Real.goldenRatio + k, ?_, ?_, ?_⟩
          · constructor <;> linarith only [hka.1, hka.2]
          · constructor <;> linarith only [hkb.1, hkb.2]
          · linarith only [hpwidth]
        · have hzta : (q 1 (a + t)).val 0 = false := Bool.eq_false_iff.mpr hta
          have hztb : (q 1 (b + t)).val 0 = false := by rw [← hst]; exact hzta
          have haB := hBinaryZero a t htpair hz0a hzta
          have hbB := hBinaryZero b t htpair hz0b hztb
          by_cases ht1 : t = 1
          · simp only [ht1, ↓reduceIte] at haB hbB
            exact ⟨alpha ^ 2 - alpha ^ 3, alpha ^ 2, haB, hbB, by
              linarith only [hCube, golden_inverse_data.2.2, hBetaBounds.1]⟩
          · simp only [ht1, ↓reduceIte] at haB hbB
            exact ⟨-(alpha ^ 3), alpha ^ 2 - alpha ^ 3, haB, hbB, by linarith⟩
  have hOrdered (heq : cuts m S = Finset.Icc 1 (G M)) (a b : ℕ)
      (hs : sigma m S a = sigma m S b) (l u : ℝ)
      (hxa : signedValue (zRow a) ∈ Set.Ioo l u)
      (hxb : signedValue (zRow b) ∈ Set.Ioo l u) (hw : u - l ≤ alpha ^ 2)
      (hxy : signedValue (zRow a) < signedValue (zRow b)) : q M a = q M b := by
    have hM : 1 ≤ M := by omega
    by_contra hq
    let x := signedValue (zRow a)
    let y := signedValue (zRow b)
    have hx := hRowInterior M hM a
    have hy := hRowInterior M hM b
    have hup : upper (q M a) < y := by
      have hle : upper (q M a) ≤ y := by
        by_contra hn
        have hi : y ∈ Set.Ioo (ell (q M a)) (upper (q M a)) :=
          ⟨lt_trans hx.1 hxy, by linarith only [hn]⟩
        exact Set.disjoint_left.mp ((hData M hM).2.2.2.1 _ _ hq) hi hy
      obtain ⟨i, j, hi1, hiM, hj1, hjM, hei, hej, hC⟩ := (hData M hM).2.2.2.2.2.1 (q M a)
      apply lt_of_le_of_ne hle
      intro he
      exact hRowAvoid b j hj1 ((congrArg (fun r : ℝ => (r : AddCircle (1 : ℝ))) he.symm).trans hej)
    obtain ⟨i, j, hi1, hiM, hj1, hjM, hei, hej, hC⟩ := (hData M hM).2.2.2.2.2.1 (q M a)
    have hjK : j ∈ cuts m S := heq.symm ▸ Finset.mem_Icc.mpr ⟨hj1, hjM⟩
    obtain ⟨t, ht, hjt⟩ := Finset.mem_biUnion.mp hjK
    have hst : q m (a + t) = q m (b + t) := congrFun hs ⟨t, ht⟩
    let p := q m (a + t)
    have haA : ((x + (t : ℝ) * Real.goldenRatio : ℝ) : AddCircle (1 : ℝ)) ∈ A p := by
      rw [AddCircle.coe_add]
      exact (natural_phase_translate a t) ▸ (hArc m hm (a + t) p).mp rfl
    have hbA : ((y + (t : ℝ) * Real.goldenRatio : ℝ) : AddCircle (1 : ℝ)) ∈ A p := by
      rw [AddCircle.coe_add]
      exact (natural_phase_translate b t) ▸ (hArc m hm (b + t) p).mp hst.symm
    have hwidth : u - l + (upper p - ell p) ≤ 1 := by
      linarith only [hw, (hWidth m hm p).1, golden_inverse_data.2.2]
    obtain ⟨z, hza, hzb⟩ := hShortLift x y l u (ell p) (upper p)
      ((t : ℝ) * Real.goldenRatio) hxa hxb hwidth haA hbA
    have hmid : ((upper (q M a) : ℝ) : AddCircle (1 : ℝ)) + gamma t ∈ A p := by
      refine ⟨upper (q M a) + (t : ℝ) * Real.goldenRatio - z, ?_, ?_⟩
      · constructor <;> linarith only [hza.1, hza.2, hzb.1, hzb.2, hx.2, hup]
      · simp only [AddCircle.coe_sub, AddCircle.coe_add, circle_integer_zero, sub_zero]
    have hcut : E j + gamma t ∈ B m := (translated_cut_mem m t j).mpr hjt
    obtain ⟨k, hk, he⟩ := hcut
    rw [hej, ← he] at hmid
    exact window_arc_avoids_cut m hm p k hk.1 hk.2 hmid
  have hDecode (heq : cuts m S = Finset.Icc 1 (G M)) (a b : ℕ)
      (hs : sigma m S a = sigma m S b) : q M a = q M b := by
    have hM : 1 ≤ M := by omega
    by_cases hM2 : 2 ≤ M
    · obtain ⟨l, u, hxa, hxb, hw⟩ := hAnchor heq hM2 a b hs
      rcases lt_trichotomy (signedValue (zRow a)) (signedValue (zRow b)) with hxy | he | hyx
      · exact hOrdered heq a b hs l u hxa hxb hw hxy
      · by_contra hq
        have hx := hRowInterior M hM a
        have hy := hRowInterior M hM b
        rw [← he] at hy
        exact Set.disjoint_left.mp ((hData M hM).2.2.2.1 _ _ hq) hx hy
      · exact (hOrdered heq b a hs.symm l u hxb hxa hw hyx).symm
    · have hM1 : M = 1 := by omega
      have hm1 : m = 1 := by omega
      have h0 := hZeroSchedule heq
      subst M
      subst m
      simpa only [sigma, Nat.add_zero] using congrFun hs ⟨0, h0⟩
  have hPredict (heq : cuts m S = Finset.Icc 1 (G M)) (a b : ℕ)
      (hq : q M a = q M b) : sigma m S a = sigma m S b := by
    have hM : 1 ≤ M := by omega
    funext t
    let p := q M a
    let pa := q m (a + t.val)
    let f (x : ℝ) : AddCircle (1 : ℝ) := (x : AddCircle (1 : ℝ)) + gamma t.val
    have hf : Continuous f := (AddCircle.continuous_mk' (1 : ℝ)).add continuous_const
    let U := f ⁻¹' A pa
    let V := ⋃ pq : {q : X m // q ≠ pa}, f ⁻¹' A pq.val
    have hU : IsOpen U := (window_arc_isOpen m pa).preimage hf
    have hV : IsOpen V := isOpen_iUnion (fun pq => (window_arc_isOpen m pq.val).preimage hf)
    have hd : Disjoint U V := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      obtain ⟨pq, hpq⟩ := Set.mem_iUnion.mp hy
      exact pq.property (window_arc_unique m hm pq.val pa (f x) hpq hx)
    have hcover : Set.Ioo (ell p) (upper p) ⊆ U ∪ V := by
      intro x hx
      have hnc : f x ∉ B m := by
        rintro ⟨j, hj, he⟩
        have hcut : t.val + j ∈ cuts m S := Finset.mem_biUnion.mpr
          ⟨t.val, t.property, Finset.mem_Icc.mpr ⟨by linarith [hj.1], by linarith [hj.2]⟩⟩
        rw [heq] at hcut
        have he' : E (t.val + j) = (x : AddCircle (1 : ℝ)) :=
          add_right_cancel ((translated_cut t.val j).trans he)
        apply window_arc_avoids_cut M hM p (t.val + j) (Finset.mem_Icc.mp hcut).1 (Finset.mem_Icc.mp hcut).2
        exact he'.symm ▸ (show (x : AddCircle (1 : ℝ)) ∈ A p from ⟨x, hx, rfl⟩)
      obtain ⟨pq, hpq⟩ := window_arc_cover m hm (f x) hnc
      by_cases he : pq = pa
      · exact Or.inl (by change f x ∈ A pa; simpa only [he] using hpq)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨pq, he⟩, hpq⟩)
    have hxa : signedValue (zRow a) ∈ U := by
      change phase (zRow a) + gamma t.val ∈ A pa
      rw [← natural_phase_translate]
      exact (hArc m hm (a + t.val) pa).mp rfl
    have hsub : Set.Ioo (ell p) (upper p) ⊆ U :=
      IsPreconnected.subset_left_of_subset_union hU hV hd hcover
        ⟨signedValue (zRow a), hRowInterior M hM a, hxa⟩ isPreconnected_Ioo
    have hy : signedValue (zRow b) ∈ Set.Ioo (ell p) (upper p) := by
      simpa only [p, ← hq] using hRowInterior M hM b
    have hbA := hsub hy
    change phase (zRow b) + gamma t.val ∈ A pa at hbA
    rw [← natural_phase_translate] at hbA
    exact ((hArc m hm (b + t.val) pa).mpr hbA).symm
  have hVbound (L : ℕ) (p : X L) : V p < G L := by
    classical
    let r : RawDigits := Finsupp.onFinset (Finset.range L)
      (fun j => if h : j < L then if p.val ⟨j, h⟩ then 1 else 0 else 0)
      (by intro j hj; by_contra hn; simp [Finset.mem_range.not.mp hn] at hj)
    have hc : CanonicalRaw r := by
      constructor
      · intro j; dsimp [r]; split <;> (try split) <;> omega
      · intro j hj
        by_cases h : j + 1 < L
        · have hjL : j < L := by omega
          have htrue : p.val ⟨j, hjL⟩ = true := by
            simpa [r, hjL] using hj
          have hn : p.val ⟨j + 1, h⟩ = false := by
            cases he : p.val ⟨j + 1, h⟩
            · rfl
            · exact False.elim (p.property j h ⟨htrue, he⟩)
          simp [r, h, hn]
        · simp [r, h]
    have hv : rawValue r = V p := by
      unfold rawValue V
      rw [Finset.sum_fin_eq_sum_range]
      dsimp [r]
      rw [Finsupp.sum_onFinset _ _ _ _ (by intros; simp)]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range.mp hj, ↓reduceDIte, D5.S0.Conventions.wValue]
      split <;> simp_all
    change V p < Nat.fib (L + 2)
    rw [← hv, rawValue_eq_sum_rawToZeckendorf]
    apply ((canonicalRaw_iff_isZeckendorfRep r).mp hc).sum_fib_lt
    intro j hj
    have hmem := List.mem_of_mem_head? hj
    rcases List.mem_append.mp hmem with hj | hj
    · change j ∈ (r.toMultiset.sort (· ≥ ·)).map (fun i => i + 2) at hj
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      have hi' : r i ≠ 0 := by simpa [Finsupp.mem_toMultiset] using hi
      have hilt : i < L := by
        by_contra hn
        simp only [r, Finsupp.onFinset_apply, dif_neg hn, ne_eq, not_true_eq_false] at hi'
      omega
    · have he : j = 0 := by simpa only [List.mem_singleton] using hj
      omega
  have hValueSmall (L n : ℕ) (hn : n < G L) : V (q L n) = n := by
    let r := rawOfZeckendorf (Nat.zeckendorf n)
    have hv : rawValue r = n := (hRawRow n).1
    have hd (j : ℕ) : (if (zRow n).val j then (1 : ℕ) else 0) = r j := by
      exact_mod_cast (hRawRow n).2 j
    have hs : r.support ⊆ Finset.range L := by
      intro j hj
      have hm : j + 2 ∈ Nat.zeckendorf n := by
        rw [← rawToZeckendorf_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf n)]
        simpa [rawToZeckendorf, Finsupp.mem_toMultiset, r] using Finsupp.mem_support_iff.mp hj
      have hle : Nat.fib (j + 2) ≤ n := by
        rw [← Nat.sum_zeckendorf_fib n]
        exact List.le_sum_of_mem (List.mem_map.mpr ⟨j + 2, hm, rfl⟩)
      have hjL : j < L := by
        by_contra h
        have hf : G L ≤ Nat.fib (j + 2) := Nat.fib_mono (by omega)
        omega
      exact Finset.mem_range.mpr hjL
    unfold V q P
    rw [Finset.sum_fin_eq_sum_range]
    trans ∑ j ∈ Finset.range L, Nat.fib (j + 2) * (if (zRow n).val j then 1 else 0)
    · apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range.mp hj, ↓reduceDIte]
    · simp_rw [hd]
      rw [← hv]
      unfold rawValue
      symm
      calc
        (∑ j ∈ r.support, r j * D5.S0.Conventions.wValue j) =
            ∑ j ∈ Finset.range L, r j * D5.S0.Conventions.wValue j := by
          apply Finset.sum_subset hs
          intro j hjL hj
          have hz : r j = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hj
          simp only [hz, zero_mul]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [D5.S0.Conventions.wValue, Nat.mul_comm]
  let eV (L : ℕ) : X L ≃ Fin (G L) := {
    toFun := fun p => ⟨V p, hVbound L p⟩
    invFun := fun n => q L n.val
    left_inv := fun p => hqV L p
    right_inv := fun n => Fin.ext (hValueSmall L n.val n.isLt)
  }
  have hXcard (L : ℕ) : Nat.card (X L) = G L :=
    (Nat.card_congr (eV L)).trans (Nat.card_fin (G L))
  refine ⟨⟨hNecessary, ?_⟩, ?_⟩
  · intro heq a b
    exact ⟨hPredict heq a b, hDecode heq a b⟩
  · intro heq
    have hf : ∀ ⦃a b : ℕ⦄, sigma m S a = sigma m S b → q M a = q M b := by
      intro a b hs
      exact hDecode heq a b hs
    let decoder : ((t : S) → X m) → Set.range (q M) :=
      Function.extend (sigma m S)
        (fun n => ⟨q M n, ⟨n, rfl⟩⟩)
        (fun _ => ⟨q M 0, ⟨0, rfl⟩⟩)
    have hFactor :
        (fun n : ℕ => (⟨q M n, ⟨n, rfl⟩⟩ : Set.range (q M))).FactorsThrough
          (sigma m S) := by
      intro a b hab
      exact Subtype.ext (hf hab)
    have hdec (n : ℕ) : (decoder (sigma m S n)).val = q M n := by
      change (Function.extend (sigma m S)
        (fun n => (⟨q M n, ⟨n, rfl⟩⟩ : Set.range (q M)))
        (fun _ => ⟨q M 0, ⟨0, rfl⟩⟩) (sigma m S n)).val = q M n
      exact congrArg Subtype.val (hFactor.extend_apply
        (fun _ => ⟨q M 0, ⟨0, rfl⟩⟩) n)
    have hActual (n : ℕ) : sigma m S (V (q M n)) = sigma m S n :=
      hPredict heq _ n (hqV M (q M n))
    let e : X M ≃ Set.range (sigma m S) := {
      toFun := fun p => ⟨sigma m S (V p), ⟨V p, rfl⟩⟩
      invFun := fun s => (decoder s.val).val
      left_inv := fun p => (hdec (V p)).trans (hqV M p)
      right_inv := by
        intro s
        obtain ⟨n, hn⟩ := s.property
        apply Subtype.ext
        change sigma m S (V (decoder s.val).val) = s.val
        rw [← hn, hdec]
        exact hActual n
    }
    have hRange : Set.range (q M) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro p
      exact ⟨V p, hqV M p⟩
    refine ⟨?_, ?_, e, (fun p => rfl), ?_, ?_⟩
    · rw [hRange]
      exact (Nat.card_congr (Equiv.Set.univ (X M))).trans (hXcard M)
    · exact (Nat.card_congr e).symm.trans (hXcard M)
    · exact hActual
    · exact hdec

end D5.S1.Digit.Infinite.SparseWindowMutualDetermination
