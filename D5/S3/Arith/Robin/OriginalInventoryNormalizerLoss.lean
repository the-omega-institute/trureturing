/- GID: D5/S3/Arith/Robin/OriginalInventoryNormalizerLoss
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/OriginalInventoryNormalizerLoss
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Complete original prime-source inventories control the literal selected normalizer loss. -/

import D5.S3.Arith.Robin.OriginalPrimeSourceOrder
import D5.S3.Arith.Robin.OriginalMovingCutRow
import Mathlib.Algebra.BigOperators.Fin

noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators

namespace D5.S3.Arith.Robin.OriginalInventoryNormalizerLoss

open D5.S3.Arith.Robin.OriginalFirstClockTransport
open D5.S3.Arith.Robin.OriginalPrimeSourceOrder
open D5.S3.Arith.Robin.OriginalMovingWindowMoment
open D5.S3.Arith.Robin.OriginalMovingCutRow
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount

private theorem canonical_maximum (X : OriginalWindow) {p : ℕ} (hp : p ∈ X.labels) :
    originalMaximizes p (canonicalSource p) := by
  have h := X.attained p hp
  simpa only [canonicalSource, dif_pos h] using Nat.find_spec h

/-- Quotients here are the complete actual inventories, not chosen factors. -/
private theorem canonical_pair (X : OriginalWindow) {p r : ℕ}
    (hp : p ∈ X.labels) (hr : r ∈ X.labels) (hpr : p < r)
    (hlatep : 243 ≤ Real.log (canonicalSource p : ℝ))
    (hlater : 243 ≤ Real.log (canonicalSource r : ℝ))
    (hlargep : Real.log (canonicalSource p : ℝ) < (p : ℝ))
    (hlarger : Real.log (canonicalSource r : ℝ) < (p : ℝ)) :
    let U := canonicalSource p / p
    let V := canonicalSource r / r
    canonicalSource p = p * U ∧ canonicalSource r = r * V ∧
    0 < U ∧ 0 < V ∧ 5040 ∣ U ∧ 5040 ∣ V ∧ U ∣ V ∧
    Real.log (canonicalSource p : ℝ) < Real.log (canonicalSource r : ℝ) ∧
    (U = V → ∀ t ∈ Icc (Real.log (canonicalSource p : ℝ))
      (Real.log (canonicalSource r : ℝ)), ∀ q : ℕ,
      U.factorization q = optimalLayerCount
        (D5.S3.Arith.Robin.ActualRobinClockCovariance.g t) q) := by
  obtain ⟨U, V, hNU, hMV, hU, hV, hcoreU, hcoreV, _, _, _, _,
      hUV, _, hclock, _, _, hinterval⟩ :=
    original_prime_source_order (X.prime_labels p hp) (X.prime_labels r hr) hpr
      (canonical_maximum X hp) (canonical_maximum X hr)
      hlatep hlater hlargep hlarger
  have hquotU : canonicalSource p / p = U := by
    rw [hNU, Nat.mul_div_cancel_left _ (X.prime_labels p hp).pos]
  have hquotV : canonicalSource r / r = V := by
    rw [hMV, Nat.mul_div_cancel_left _ (X.prime_labels r hr).pos]
  dsimp only
  rw [hquotU, hquotV]
  exact ⟨hNU, hMV, hU, hV, hcoreU, hcoreV, hUV, hclock, hinterval⟩

private theorem enumerated_mem (X : OriginalWindow) {n : ℕ}
    (p : Fin (n + 1) → ℕ) (hlabels : X.labels = Finset.univ.image p)
    (i : Fin (n + 1)) : p i ∈ X.labels := by
  rw [hlabels]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

private theorem enumerated_adjacent (X : OriginalWindow) {n : ℕ}
    (p : Fin (n + 1) → ℕ) (hp : StrictMono p)
    (hlabels : X.labels = Finset.univ.image p) (i : Fin n) :
    ∀ q ∈ X.labels, ¬(p i.castSucc < q ∧ q < p i.succ) := by
  intro q hq hbetween
  rw [hlabels] at hq
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
  have hlo : i.castSucc < j := (hp.lt_iff_lt).mp hbetween.1
  have hhi : j < i.succ := (hp.lt_iff_lt).mp hbetween.2
  have := hlo
  have := hhi
  simp only [Fin.lt_iff_val_lt_val, Fin.val_castSucc, Fin.val_succ] at *
  omega

private theorem adjacent_indices {n : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : StrictMono p) {a b : Fin (n + 1)} (hab : p a < p b)
    (hadj : ∀ j : Fin (n + 1), ¬(p a < p j ∧ p j < p b)) :
    ∃ i : Fin n, a = i.castSucc ∧ b = i.succ := by
  have hab' : a < b := (hp.lt_iff_lt).mp hab
  have hstep : b.val = a.val + 1 := by
    by_contra h
    have hk : a.val + 1 < n + 1 := by omega
    have hleft : a < (⟨a.val + 1, hk⟩ : Fin (n + 1)) := by
      simp only [Fin.lt_iff_val_lt_val]; omega
    have hright : (⟨a.val + 1, hk⟩ : Fin (n + 1)) < b := by
      simp only [Fin.lt_iff_val_lt_val]; omega
    exact hadj ⟨a.val + 1, hk⟩ ⟨hp hleft, hp hright⟩
  refine ⟨⟨a.val, by omega⟩, ?_, ?_⟩
  · apply Fin.ext; rfl
  · apply Fin.ext; simpa using hstep

private theorem sum_clock_differences {n : ℕ} (v : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (v i.succ - v i.castSucc)) = v (Fin.last n) - v 0 := by
  have hfirst := Fin.sum_univ_succ v
  have hlast := Fin.sum_univ_castSucc v
  rw [Finset.sum_sub_distrib]
  linarith

/-- Closed adjacent intervals are replaced only up to null endpoints. -/
private theorem integral_selected_cells {n : ℕ} (T : Fin (n + 1) → ℝ)
    (hT : Monotone T) (good : Finset (Fin n)) {ell R : ℝ}
    (hclocks : ∀ i, T i ∈ Icc ell R) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc ell R)) :
    (∫ t in ⋃ i ∈ good, Icc (T i.castSucc) (T i.succ), f t) =
      ∑ i ∈ good, ∫ t in Icc (T i.castSucc) (T i.succ), f t := by
  have hae : (⋃ i ∈ good, Ioc (T i.castSucc) (T i.succ)) =ᵐ[volume]
      (⋃ i ∈ good, Icc (T i.castSucc) (T i.succ)) :=
    ae_eq_set_biUnion good.countable_toSet (fun _ _ => Ioc_ae_eq_Icc)
  rw [← setIntegral_congr_set hae]
  have hdisj : Set.Pairwise (↑good)
      (Disjoint on (fun i : Fin n => Ioc (T i.castSucc) (T i.succ))) := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · apply Ioc_disjoint_Ioc_of_le
      apply hT
      change i.val + 1 ≤ j.val
      omega
    · apply Disjoint.symm
      apply Ioc_disjoint_Ioc_of_le
      apply hT
      change j.val + 1 ≤ i.val
      omega
  rw [integral_biUnion_finset good (fun _ _ => measurableSet_Ioc) hdisj]
  · apply Finset.sum_congr rfl
    intro i _
    exact (integral_Icc_eq_integral_Ioc).symm
  · intro i _
    exact hf.mono_set (fun t ht =>
      ⟨(hclocks i.castSucc).1.trans ht.1.le, ht.2.trans (hclocks i.succ).2⟩)

private theorem integral_cell_difference {ell R a b : ℝ} {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc ell R)) (ha : a ∈ Icc ell R)
    (hb : b ∈ Icc ell R) (hab : a ≤ b) :
    (∫ t in Icc a b, f t) = (∫ t in Icc ell b, f t) -
      (∫ t in Icc ell a, f t) := by
  have hia : IntervalIntegrable f volume ell a :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ha.1).mpr
      (hf.mono_set (fun _ ht => ⟨ht.1, ht.2.trans ha.2⟩))
  have hiab : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (hf.mono_set (fun _ ht => ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩))
  have h := intervalIntegral.integral_add_adjacent_intervals hia hiab
  rw [intervalIntegral.integral_of_le ha.1, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hb.1] at h
  simp only [← integral_Icc_eq_integral_Ioc] at h
  linarith

/-- This identity includes both collars and also works for a singleton clock. -/
private theorem integral_chain_partition {n : ℕ} (T : Fin (n + 1) → ℝ)
    (hT : Monotone T) {ell R : ℝ} (hclocks : ∀ i, T i ∈ Icc ell R)
    {f : ℝ → ℝ} (hf : IntegrableOn f (Icc ell R)) :
    (∫ t in Icc ell R, f t) =
      (∫ t in Icc ell (T 0), f t) +
      (∑ i : Fin n, ∫ t in Icc (T i.castSucc) (T i.succ), f t) +
      (∫ t in Icc (T (Fin.last n)) R, f t) := by
  have hsum : (∑ i : Fin n, ∫ t in Icc (T i.castSucc) (T i.succ), f t) =
      (∫ t in Icc ell (T (Fin.last n)), f t) - (∫ t in Icc ell (T 0), f t) := by
    calc
      _ = ∑ i : Fin n, ((∫ t in Icc ell (T i.succ), f t) -
          (∫ t in Icc ell (T i.castSucc), f t)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact integral_cell_difference hf (hclocks _) (hclocks _)
          (hT (by change i.val ≤ i.val + 1; omega))
      _ = _ := sum_clock_differences (fun i => ∫ t in Icc ell (T i), f t)
  have horder : ell ≤ R := (hclocks 0).1.trans (hclocks 0).2
  have hright := integral_cell_difference hf (hclocks (Fin.last n))
    (show R ∈ Icc ell R from ⟨horder, le_rfl⟩) (hclocks _).2
  linarith

private theorem complementary_sum {n : ℕ} (U : Fin (n + 1) → ℕ)
    (a : Fin n → ℝ) :
    (∑ i : Fin n, a i) -
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => U i.castSucc = U i.succ), a i) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => U i.castSucc ≠ U i.succ), a i := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun i : Fin n => U i.castSucc = U i.succ) (f := a)
  linarith

/-- The literal full selection and the omitted normalizer are controlled by
complete integer inventories. No signed moment or positive denominator is assumed. -/
theorem original_inventory_normalizer_loss
    (X : OriginalWindow) {n : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : StrictMono p) (hlabels : X.labels = Finset.univ.image p)
    {ell R : ℝ} (hcomplete : X.labels = originalLabelWindow ell)
    (hell : 243 ≤ ell)
    (hclocks : ∀ i : Fin (n + 1),
      Real.log (canonicalSource (p i) : ℝ) ∈ Icc ell R)
    (hlarge : R < (p 0 : ℝ)) :
    let T : Fin (n + 1) → ℝ := fun i => Real.log (canonicalSource (p i) : ℝ)
    let U : Fin (n + 1) → ℕ := fun i => canonicalSource (p i) / p i
    let bad := Finset.univ.filter (fun i : Fin n => U i.castSucc ≠ U i.succ)
    let good := Finset.univ.filter (fun i : Fin n => U i.castSucc = U i.succ)
    let D := Real.log (U (Fin.last n) : ℝ) - Real.log (U 0 : ℝ)
    let C := (T 0 - ell) + (R - T (Fin.last n))
    StrictMono T ∧
    (∀ i, 0 < U i ∧ 5040 ∣ U i ∧ canonicalSource (p i) = p i * U i) ∧
    (∀ i : Fin n, U i.castSucc ∣ U i.succ ∧
      (GoodEdge X (p i.castSucc) (p i.succ) ↔ U i.castSucc = U i.succ)) ∧
    selectedDomain X = (⋃ i ∈ good, Icc (T i.castSucc) (T i.succ)) ∧
    (volume (Icc ell R \ selectedDomain X)).toReal =
      C + ∑ i ∈ bad, (T i.succ - T i.castSucc) ∧
    (volume (Icc ell R \ selectedDomain X)).toReal ≤ C + 2 * D ∧
    ∀ x : ℝ,
      windowMass ell R x - (∫ t in selectedDomain X, kernel t x) =
        windowMass ell (T 0) x +
          (∑ i ∈ bad, windowMass (T i.castSucc) (T i.succ) x) +
          windowMass (T (Fin.last n)) R x ∧
      0 ≤ windowMass ell R x - (∫ t in selectedDomain X, kernel t x) ∧
      windowMass ell R x - (∫ t in selectedDomain X, kernel t x) ≤
        ell ^ (-3 / 10 : ℝ) * (C + 2 * D) := by
  let T : Fin (n + 1) → ℝ := fun i => Real.log (canonicalSource (p i) : ℝ)
  let U : Fin (n + 1) → ℕ := fun i => canonicalSource (p i) / p i
  let bad := Finset.univ.filter (fun i : Fin n => U i.castSucc ≠ U i.succ)
  let good := Finset.univ.filter (fun i : Fin n => U i.castSucc = U i.succ)
  let D := Real.log (U (Fin.last n) : ℝ) - Real.log (U 0 : ℝ)
  let C := (T 0 - ell) + (R - T (Fin.last n))
  change StrictMono T ∧ _
  have hmem := enumerated_mem X p hlabels
  have hprime (i : Fin (n + 1)) : (p i).Prime := X.prime_labels _ (hmem i)
  have hlate (i : Fin (n + 1)) : 243 ≤ T i := hell.trans (hclocks i).1
  have hsep (i j : Fin (n + 1)) : T i < (p j : ℝ) := by
    have hmin : (p 0 : ℝ) ≤ p j := by exact_mod_cast hp.monotone (Fin.zero_le j)
    exact (hclocks i).2.trans_lt (hlarge.trans_le hmin)
  have hpair (i j : Fin (n + 1)) (hij : i < j) :=
    canonical_pair X (hmem i) (hmem j) (hp hij)
      (hlate i) (hlate j) (hsep i i) (hsep j i)
  have hT : StrictMono T := by
    intro i j hij
    exact (hpair i j hij).2.2.2.2.2.2.2.1
  have hinventory (i : Fin (n + 1)) :
      0 < U i ∧ 5040 ∣ U i ∧ canonicalSource (p i) = p i * U i := by
    obtain ⟨_, V, hN, hV, hcore, _, _⟩ :=
      D5.S3.Arith.Robin.RestrictedDivisorStrictInventory.original_maximum_strict_inventory
        (hprime i) (canonical_maximum X (hmem i)) (hlate i) (hsep i i)
    have hquot : U i = V := by
      dsimp [U]
      rw [hN, Nat.mul_div_cancel_left _ (hprime i).pos]
    simpa only [hquot] using (show 0 < V ∧ 5040 ∣ V ∧
      canonicalSource (p i) = p i * V from ⟨hV, hcore, hN⟩)
  have hadj := enumerated_adjacent X p hp hlabels
  have hedge (i : Fin n) : U i.castSucc ∣ U i.succ ∧
      (GoodEdge X (p i.castSucc) (p i.succ) ↔ U i.castSucc = U i.succ) := by
    have hi : i.castSucc < i.succ := by change i.val < i.val + 1; omega
    obtain ⟨hN, hM, hU, hV, hcoreU, hcoreV, hUV, hclock, hinterval⟩ :=
      hpair i.castSucc i.succ hi
    refine ⟨hUV, ?_⟩
    constructor
    · rintro ⟨_, _, _, _, V, _, _, hNV, hMV, _⟩
      have hpV : U i.castSucc = V := by
        dsimp [U]; rw [hNV, Nat.mul_div_cancel_left _ (hprime i.castSucc).pos]
      have hrV : U i.succ = V := by
        dsimp [U]; rw [hMV, Nat.mul_div_cancel_left _ (hprime i.succ).pos]
      exact hpV.trans hrV.symm
    · intro heq
      exact ⟨hmem _, hmem _, hp hi, hadj i, U i.castSucc, hU, hcoreU,
        hN, by simpa only [heq] using hM, hclock, hinterval heq⟩
  have hselected : selectedDomain X = ⋃ i ∈ good, Icc (T i.castSucc) (T i.succ) := by
    ext t
    constructor
    · intro ht
      obtain ⟨e, he, ht⟩ := mem_iUnion₂.mp ht
      have hegood : GoodEdge X e.1 e.2 := (Finset.mem_filter.mp he).2
      have ha := hegood.1
      have hb := hegood.2.1
      rw [hlabels] at ha hb
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp ha
      obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hb
      have hab : p a < p b := by simpa only [ha, hb] using hegood.2.2.1
      obtain ⟨i, hai, hbi⟩ := adjacent_indices p hp hab (fun j => by
        simpa only [ha, hb] using hegood.2.2.2.1 (p j) (hmem j))
      have heq : U i.castSucc = U i.succ := (hedge i).2.mp (by
        simpa only [← hai, ← hbi, ha, hb] using hegood)
      apply mem_iUnion₂.mpr
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩, ?_⟩
      simpa only [T, ← hai, ← hbi, ha, hb] using ht
    · intro ht
      obtain ⟨i, hi, ht⟩ := mem_iUnion₂.mp ht
      have heq := (Finset.mem_filter.mp hi).2
      have hegood := (hedge i).2.mpr heq
      apply mem_iUnion₂.mpr
      refine ⟨(p i.castSucc, p i.succ), ?_, ht⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hmem _, hmem _⟩, hegood⟩
  have hSmeas : MeasurableSet (selectedDomain X) := by
    rw [hselected]
    exact good.measurableSet_biUnion (fun _ _ => measurableSet_Icc)
  have hSsub : selectedDomain X ⊆ Icc ell R := by
    rw [hselected]
    intro t ht
    obtain ⟨i, _, ht⟩ := mem_iUnion₂.mp ht
    exact ⟨(hclocks i.castSucc).1.trans ht.1, ht.2.trans (hclocks i.succ).2⟩
  have hJfinite : volume (Icc ell R) ≠ ⊤ := isCompact_Icc.measure_ne_top
  have hOmfinite : volume (Icc ell R \ selectedDomain X) ≠ ⊤ :=
    ne_top_of_le_ne_top hJfinite (measure_mono sdiff_subset)
  have hOmmeas := measurableSet_Icc.diff hSmeas
  have hpartition (f : ℝ → ℝ) (hf : IntegrableOn f (Icc ell R)) :
      (∫ t in Icc ell R, f t) - (∫ t in selectedDomain X, f t) =
        (∫ t in Icc ell (T 0), f t) +
          (∑ i ∈ bad, ∫ t in Icc (T i.castSucc) (T i.succ), f t) +
          (∫ t in Icc (T (Fin.last n)) R, f t) := by
    have hfull := integral_chain_partition T hT.monotone hclocks hf
    have hsel : (∫ t in selectedDomain X, f t) =
        ∑ i ∈ good, ∫ t in Icc (T i.castSucc) (T i.succ), f t := by
      rw [hselected]
      exact integral_selected_cells T hT.monotone good hclocks hf
    have hsplit := complementary_sum U
      (fun i => ∫ t in Icc (T i.castSucc) (T i.succ), f t)
    linarith
  have hlength : (volume (Icc ell R \ selectedDomain X)).toReal =
      C + ∑ i ∈ bad, (T i.succ - T i.castSucc) := by
    have hid := setIntegral_sdiff hSmeas
      (integrableOn_const (C := (1 : ℝ)) hJfinite) hSsub
    have hpart := hpartition (fun _ => 1) (integrableOn_const hJfinite)
    rw [← hid] at hpart
    simp only [setIntegral_const, smul_eq_mul, mul_one] at hpart
    have hleft : volume.real (Icc ell (T 0)) = T 0 - ell :=
      Real.volume_real_Icc_of_le (hclocks 0).1
    have hright : volume.real (Icc (T (Fin.last n)) R) = R - T (Fin.last n) :=
      Real.volume_real_Icc_of_le (hclocks _).2
    have hcell (i : Fin n) : volume.real (Icc (T i.castSucc) (T i.succ)) =
        T i.succ - T i.castSucc :=
      Real.volume_real_Icc_of_le (hT.monotone (by change i.val ≤ i.val + 1; omega))
    simp only [hleft, hright, hcell] at hpart
    dsimp [C]
    linarith
  have hbadbound (i : Fin n) (hi : i ∈ bad) :
      T i.succ - T i.castSucc ≤
        2 * (Real.log (U i.succ : ℝ) - Real.log (U i.castSucc : ℝ)) := by
    have hpr : p i.castSucc < p i.succ := hp (by change i.val < i.val + 1; omega)
    have hplain := original_label_window_no_internal_prime
      (by rw [← hcomplete]; exact hmem i.castSucc)
      (by rw [← hcomplete]; exact hmem i.succ) hpr
      (fun q hq => hadj i q (by rwa [hcomplete]))
    obtain ⟨V, W, hN, hM, _, _, _, _, _, hgap⟩ :=
      original_prime_source_inventory_gap (hprime i.castSucc) (hprime i.succ) hpr
        (canonical_maximum X (hmem i.castSucc)) (canonical_maximum X (hmem i.succ))
        (hlate i.castSucc) (hlate i.succ) (hsep i.castSucc i.castSucc)
        (hsep i.succ i.castSucc) hplain
    have hV : V = U i.castSucc := by
      dsimp [U]
      rw [hN, Nat.mul_div_cancel_left _ (hprime i.castSucc).pos]
    have hW : W = U i.succ := by
      dsimp [U]
      rw [hM, Nat.mul_div_cancel_left _ (hprime i.succ).pos]
    have hne : V ≠ W := by
      simpa only [hV, hW] using (Finset.mem_filter.mp hi).2
    simpa only [hV, hW] using hgap hne
  have htotalGrowth : (∑ i ∈ bad,
      (Real.log (U i.succ : ℝ) - Real.log (U i.castSucc : ℝ))) = D := by
    calc
      _ = ∑ i : Fin n, (Real.log (U i.succ : ℝ) - Real.log (U i.castSucc : ℝ)) := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i _ hi
        have heq : U i.castSucc = U i.succ := by
          by_contra hne
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
        simp only [heq, sub_self]
      _ = D := sum_clock_differences (fun i => Real.log (U i : ℝ))
  have hsumBound : (∑ i ∈ bad, (T i.succ - T i.castSucc)) ≤ 2 * D := by
    calc
      _ ≤ ∑ i ∈ bad, 2 * (Real.log (U i.succ : ℝ) - Real.log (U i.castSucc : ℝ)) :=
        Finset.sum_le_sum hbadbound
      _ = 2 * D := by rw [← Finset.mul_sum, htotalGrowth]
  have hlengthBound : (volume (Icc ell R \ selectedDomain X)).toReal ≤ C + 2 * D := by
    rw [hlength]
    linarith
  refine ⟨hT, hinventory, hedge, hselected, hlength, hlengthBound, ?_⟩
  intro x
  have hkint := kernel_integrableOn (x := x) (by linarith : 4 ≤ ell)
  have hmass := hpartition (fun t => kernel t x) hkint
  have hloss : windowMass ell R x - (∫ t in selectedDomain X, kernel t x) =
      ∫ t in Icc ell R \ selectedDomain X, kernel t x :=
    (setIntegral_sdiff hSmeas hkint hSsub).symm
  have hnonneg : 0 ≤ windowMass ell R x - (∫ t in selectedDomain X, kernel t x) := by
    rw [hloss]
    exact setIntegral_nonneg hOmmeas (fun t ht =>
      kernel_nonneg (by linarith [ht.1.1] : 4 ≤ t))
  have hupper : windowMass ell R x - (∫ t in selectedDomain X, kernel t x) ≤
      ell ^ (-3 / 10 : ℝ) * (volume (Icc ell R \ selectedDomain X)).toReal := by
    rw [hloss]
    have hpoint (t : ℝ) (ht : t ∈ Icc ell R \ selectedDomain X) :
        kernel t x ≤ ell ^ (-3 / 10 : ℝ) := by
      have ht4 : 4 ≤ t := by linarith [ht.1.1]
      exact (kernel_le_height ht4).trans ((height_bounds ht4).2.trans
        (Real.rpow_le_rpow_of_nonpos (by linarith : 0 < ell) ht.1.1 (by norm_num)))
    have hle := setIntegral_mono_on (hkint.mono_set sdiff_subset)
      (integrableOn_const (C := ell ^ (-3 / 10 : ℝ)) hOmfinite) hOmmeas hpoint
    simpa only [setIntegral_const, smul_eq_mul, mul_comm] using hle
  refine ⟨hmass, hnonneg, hupper.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hlengthBound (Real.rpow_nonneg (by linarith) _)

end D5.S3.Arith.Robin.OriginalInventoryNormalizerLoss

#print axioms D5.S3.Arith.Robin.OriginalInventoryNormalizerLoss.original_inventory_normalizer_loss
