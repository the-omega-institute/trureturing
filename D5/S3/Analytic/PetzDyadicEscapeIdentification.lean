/- GID: D5/S3/Analytic/PetzDyadicEscapeIdentification
   generality: G
   mirror-B: D5/B/S3/Analytic/PetzDyadicEscapeIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Exact identification of Petz rate laws from the first moment and distinct scales. -/

import D5.S3.Analytic.ExponentialSum.DescartesRule
import D5.S3.Analytic.PetzDyadicEscapeSpectrum
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.ChainOfFn
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Exact identification of the finite Petz rate profile

On the sorted common grid, the difference of the two Laplace transforms
has a stationary zero at scale zero when mass and first moment agree.
-/

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.Analytic.PetzDyadicEscapeIdentification

open PetzDyadicEscapeSpectrum
open ExponentialSum.DescartesRule (exponentialSum zero_bound_with_stationary_root)

private theorem signVariations_ofFn_le {n : ℕ} (a : Fin n → ℝ) :
    (List.ofFn a).signVariations ≤ n - 1 := by
  unfold List.signVariations
  apply Nat.sub_le_sub_right _ 1
  calc
    _ ≤ ((List.ofFn a).map SignType.sign |>.filter (· ≠ 0)).length :=
      (List.destutter_sublist _ _).length_le
    _ ≤ ((List.ofFn a).map SignType.sign).length := List.length_filter_le _ _
    _ = n := by simp

private theorem tiltedRateMoment_eq_of_observation {ι : Type*} [Fintype ι]
    (rates w v : ι → ℝ) {s : ℝ} (hs : s ≠ 0)
    (hmass : rateMoment rates w 0 = rateMoment rates v 0)
    (hmean : rateMoment rates w 1 = rateMoment rates v 1)
    (hobs : rateProfile rates w s = rateProfile rates v s) :
    tiltedRateMoment rates w 0 s = tiltedRateMoment rates v 0 s := by
  rw [rateProfile_eq_laplace, rateProfile_eq_laplace, hmass, hmean] at hobs
  have h := (div_left_inj' hs).mp hobs
  linarith

/-- Equal mass and first moment, together with at least `2 * m - 2` distinct
positive scale observations, identify weights with at most `m` nonzero entries
per law on a sorted common rate grid. For `m = 1` the scales may be empty. -/
theorem rateProfile_identifies_weights
    {m n : ℕ} (hm : 1 ≤ m)
    (rates w v : Fin n → ℝ) (hr : StrictMono rates)
    (scales : Finset ℝ) (hcount : 2 * m - 2 ≤ scales.card)
    (hpos : ∀ s ∈ scales, 0 < s)
    (hw : (Finset.univ.filter (fun i => w i ≠ 0)).card ≤ m)
    (hv : (Finset.univ.filter (fun i => v i ≠ 0)).card ≤ m)
    (hmass : rateMoment rates w 0 = rateMoment rates v 0)
    (hmean : rateMoment rates w 1 = rateMoment rates v 1)
    (hobs : ∀ s ∈ scales, rateProfile rates w s = rateProfile rates v s) :
    w = v := by
  classical
  by_contra hne
  let support := Finset.univ.filter (fun i => w i - v i ≠ 0)
  let index := support.orderEmbOfFin rfl
  let a : Fin support.card → ℝ := fun i => w (index i) - v (index i)
  let μ : Fin support.card → ℝ := fun i => -rates (index i)
  have hsupport : support.Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, sub_ne_zero.mpr hi⟩⟩
  have ha : ∃ i, a i ≠ 0 := by
    let i : Fin support.card := ⟨0, Finset.card_pos.mpr hsupport⟩
    exact ⟨i, (Finset.mem_filter.mp (support.orderEmbOfFin_mem rfl i)).2⟩
  have hμ : StrictAnti μ := fun _ _ hij => neg_lt_neg (hr (index.strictMono hij))
  have hsupp_le : support.card ≤ 2 * m := by
    have hsub : support ⊆ (Finset.univ.filter (fun i => w i ≠ 0)) ∪
        (Finset.univ.filter (fun i => v i ≠ 0)) := by
      intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra! h
      exact hi' (by rw [h.1, h.2, sub_self])
    have hu := Finset.card_union_le (Finset.univ.filter (fun i => w i ≠ 0))
      (Finset.univ.filter (fun i => v i ≠ 0))
    have hs := Finset.card_le_card hsub
    omega
  have htransform : exponentialSum a μ = fun s =>
      tiltedRateMoment rates w 0 s - tiltedRateMoment rates v 0 s := by
    funext s
    simp only [exponentialSum, tiltedRateMoment, pow_zero, mul_one, a, μ, mul_comm _ s, mul_neg,
      ← Finset.sum_sub_distrib, ← sub_mul]
    calc
      _ = ∑ i ∈ support, (w i - v i) * Real.exp (-(s * rates i)) := by
        conv_rhs =>
          rw [← support.map_orderEmbOfFin_univ (k := support.card) rfl, Finset.sum_map]
        rfl
      _ = _ := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        have hzero : w i - v i = 0 := by simpa [support] using hi
        rw [hzero, zero_mul]
  have hz : (0 : ℝ) ∉ scales := fun h => (lt_irrefl 0) (hpos 0 h)
  have hvanish : ∀ s ∈ insert 0 scales, exponentialSum a μ s = 0 := by
    intro s hs
    rw [htransform]
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact sub_eq_zero.mpr hmass
    · exact sub_eq_zero.mpr
        (tiltedRateMoment_eq_of_observation rates w v (hpos s hs).ne' hmass hmean (hobs s hs))
  have hstationary : deriv (exponentialSum a μ) 0 = 0 := by
    rw [htransform]
    have hd := ((hasDerivAt_tiltedRateMoment rates w 0 0).sub
      (hasDerivAt_tiltedRateMoment rates v 0 0)).deriv
    exact hd.trans (sub_eq_zero.mpr (congrArg Neg.neg hmean))
  have hbound := zero_bound_with_stationary_root a μ hμ ha (insert 0 scales)
    (Finset.mem_insert_self _ _) hvanish hstationary
  rw [Finset.card_insert_of_notMem hz] at hbound
  have hvar := signVariations_ofFn_le a
  omega

private theorem alternates_of_full_signVariations {n : ℕ} (hn : 2 ≤ n) (a : Fin n → ℝ)
    (h : n - 1 ≤ (List.ofFn a).signVariations) :
    (∀ i, a i ≠ 0) ∧ ∀ i j, i.val + 1 = j.val → SignType.sign (a i) ≠ SignType.sign (a j) := by
  let signs := (List.ofFn a).map SignType.sign
  let nonzero := signs.filter (· ≠ 0)
  have hfilter : List.Sublist nonzero signs := List.filter_sublist
  have hdestutter := List.destutter_sublist (· ≠ ·) nonzero
  have hlen : signs.length = n := by simp [signs]
  have hfull : signs.length ≤ (nonzero.destutter (· ≠ ·)).length := by
    change n - 1 ≤ (nonzero.destutter (· ≠ ·)).length - 1 at h
    omega
  have hnonzero := hfilter.eq_of_length_le (hfull.trans hdestutter.length_le)
  have hnodup := (hdestutter.trans hfilter).eq_of_length_le hfull
  constructor
  · intro i hi
    have hmem : SignType.sign (a i) ∈ signs :=
      List.mem_map.mpr ⟨a i, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩
    rw [← hnonzero] at hmem
    have hsign : SignType.sign (a i) ≠ 0 := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp hmem).2
    exact hsign (sign_eq_zero_iff.mpr hi)
  · have hchain : signs.IsChain (· ≠ ·) := hnodup ▸ List.isChain_destutter _ _
    have hchain' : (List.ofFn (fun i => SignType.sign (a i))).IsChain (· ≠ ·) := by
      simpa only [signs, List.map_ofFn, Function.comp_def] using hchain
    have hstep := List.isChain_ofFn.mp hchain'
    intro i j hij
    simpa only [hij] using hstep i.val (hij.symm ▸ j.isLt)

private theorem card_filter_sign_le {m : ℕ} (a : Fin (2 * m) → ℝ)
    (hstep : ∀ i j, i.val + 1 = j.val → SignType.sign (a i) ≠ SignType.sign (a j))
    (sign : SignType) : (Finset.univ.filter (fun i => SignType.sign (a i) = sign)).card ≤ m := by
  let pair (i : Fin (2 * m)) : Fin m := ⟨i.val / 2, by have hi := i.isLt; omega⟩
  calc
    _ ≤ (Finset.univ : Finset (Fin m)).card := by
      refine Finset.card_le_card_of_injOn pair (fun _ _ => Finset.mem_univ _) ?_
      intro i hi j hj heq
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      have hdiv : i.val / 2 = j.val / 2 := congrArg Fin.val heq
      rcases lt_trichotomy i.val j.val with h | h | h
      · exact (hstep i j (by omega) (hi'.trans hj'.symm)).elim
      · exact Fin.ext h
      · exact (hstep j i (by omega) (hj'.trans hi'.symm)).elim
    _ = m := by simp

/-- For any `2 * m - 3` distinct positive scales, two probability laws on any
strictly increasing grid of `2 * m` rates have identical observations and first
moment, with disjoint supports of exactly `m` rates each. -/
theorem rateProfile_query_count_sharp
    {m : ℕ} (hm : 2 ≤ m) (rates : Fin (2 * m) → ℝ) (hr : StrictMono rates)
    (scales : Finset ℝ) (hcount : scales.card = 2 * m - 3) (hpos : ∀ s ∈ scales, 0 < s) :
    ∃ w v : Fin (2 * m) → ℝ,
      w ≠ v ∧ (∀ i, 0 ≤ w i ∧ 0 ≤ v i ∧ w i * v i = 0) ∧
      (Finset.univ.filter (fun i => w i ≠ 0)).card = m ∧
      (Finset.univ.filter (fun i => v i ≠ 0)).card = m ∧
      (∑ i, w i) = 1 ∧ (∑ i, v i) = 1 ∧
      rateMoment rates w 1 = rateMoment rates v 1 ∧
      (∀ s ∈ scales, rateProfile rates w s = rateProfile rates v s) := by
  classical
  let observations : Matrix (Fin 2 ⊕ ↥scales) (Fin (2 * m)) ℝ :=
    Sum.elim (fun k i => rates i ^ k.val) (fun s i => Real.exp (-((s : ℝ) * rates i)))
  have hdim : Module.finrank ℝ ((Fin 2 ⊕ ↥scales) → ℝ) <
      Module.finrank ℝ (Fin (2 * m) → ℝ) := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_coe, hcount]
    omega
  obtain ⟨a, ha, hane⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := observations.mulVecLin) hdim)
  have hrow := LinearMap.mem_ker.mp ha
  have hmoment (k : Fin 2) : rateMoment rates a k.val = 0 := by
    have hk := congrFun hrow (.inl k)
    change (∑ i, rates i ^ k.val * a i) = 0 at hk
    simpa only [rateMoment_eq_sum, mul_comm] using hk
  have hlaplace (s : ℝ) (hs : s ∈ scales) : tiltedRateMoment rates a 0 s = 0 := by
    have hk := congrFun hrow (.inr ⟨s, hs⟩)
    change (∑ i, Real.exp (-(s * rates i)) * a i) = 0 at hk
    simpa only [tiltedRateMoment, pow_zero, mul_one, mul_comm] using hk
  let μ : Fin (2 * m) → ℝ := fun i => -rates i
  have htransform : exponentialSum a μ = tiltedRateMoment rates a 0 := by
    funext s
    simp only [exponentialSum, tiltedRateMoment, pow_zero, mul_one, μ, mul_comm _ s, mul_neg]
  have hvanish : ∀ s ∈ insert 0 scales, exponentialSum a μ s = 0 := by
    intro s hs
    rw [htransform]
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact hmoment 0
    · exact hlaplace s hs
  have hstationary : deriv (exponentialSum a μ) 0 = 0 := by
    rw [htransform, (hasDerivAt_tiltedRateMoment rates a 0 0).deriv]
    exact neg_eq_zero.mpr (hmoment 1)
  have hz : (0 : ℝ) ∉ scales := fun h => (lt_irrefl 0) (hpos 0 h)
  have hcoeff := Function.ne_iff.mp hane
  have hbound := zero_bound_with_stationary_root a μ (fun _ _ hij => neg_lt_neg (hr hij))
    hcoeff (insert 0 scales) (Finset.mem_insert_self _ _) hvanish hstationary
  rw [Finset.card_insert_of_notMem hz, hcount] at hbound
  obtain ⟨hfull, hstep⟩ := alternates_of_full_signVariations (by omega) a (by omega)
  -- Each consecutive pair contributes one index to each support.
  let positive := Finset.univ.filter (fun i => SignType.sign (a i) = 1)
  let negative := Finset.univ.filter (fun i => SignType.sign (a i) = -1)
  have hpos_le : positive.card ≤ m := card_filter_sign_le a hstep 1
  have hneg_le : negative.card ≤ m := card_filter_sign_le a hstep (-1)
  have hdisjoint : Disjoint positive negative := by
    refine Finset.disjoint_left.mpr ?_
    intro i hi hj
    exact (by decide : (1 : SignType) ≠ -1)
      ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)
  have hcover : positive ∪ negative = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    rcases lt_or_gt_of_ne (hfull i) with hi | hi
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, sign_neg hi⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, sign_pos hi⟩)
  have htotal := Finset.card_union_of_disjoint hdisjoint
  rw [hcover, Finset.card_univ, Fintype.card_fin] at htotal
  -- Normalize the two parts of the kernel vector by their common mass.
  let mass := ∑ i, max (a i) 0
  have hsplit (i : Fin (2 * m)) : max (a i) 0 - max (-a i) 0 = a i := by
    rcases le_total 0 (a i) with hi | hi
    · rw [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi), sub_zero]
    · rw [max_eq_right hi, max_eq_left (neg_nonneg.mpr hi), zero_sub, neg_neg]
  have hmass : (∑ i, max (-a i) 0) = mass := by
    have hsum : (∑ i, (max (a i) 0 - max (-a i) 0)) = ∑ i, a i :=
      Finset.sum_congr rfl (fun i _ => hsplit i)
    rw [Finset.sum_sub_distrib] at hsum
    have hzero : (∑ i, a i) = 0 := by simpa [rateMoment_eq_sum] using hmoment 0
    exact (sub_eq_zero.mp (hsum.trans hzero)).symm
  have hmass_pos : 0 < mass := by
    have hc : positive.Nonempty := Finset.card_pos.mp (show 0 < positive.card by omega)
    obtain ⟨i, hi⟩ := hc
    have hi' : 0 < a i := sign_eq_one_iff.mp (Finset.mem_filter.mp hi).2
    exact Finset.sum_pos' (fun _ _ => le_max_right _ _)
      ⟨i, Finset.mem_univ _, hi'.trans_le (le_max_left _ _)⟩
  let w : Fin (2 * m) → ℝ := fun i => max (a i) 0 / mass
  let v : Fin (2 * m) → ℝ := fun i => max (-a i) 0 / mass
  have hdiff (i) : w i - v i = a i / mass := by
    simp only [w, v, ← sub_div, hsplit]
  have hw : Finset.univ.filter (fun i => w i ≠ 0) = positive := by
    ext i
    simp [w, positive, hmass_pos.ne', sign_eq_one_iff, not_le]
  have hv : Finset.univ.filter (fun i => v i ≠ 0) = negative := by
    ext i
    simp [v, negative, hmass_pos.ne', sign_eq_neg_one_iff, not_le]
  have hsum_w : (∑ i, w i) = 1 := by simp [w, ← Finset.sum_div, mass, hmass_pos.ne']
  have hsum_v : (∑ i, v i) = 1 := by simp [v, ← Finset.sum_div, hmass, hmass_pos.ne']
  have hsum_diff (f : Fin (2 * m) → ℝ) :
      (∑ i, w i * f i) - (∑ i, v i * f i) = (∑ i, a i * f i) / mass := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [← sub_mul, hdiff, div_mul_eq_mul_div]
  have hmean : rateMoment rates w 1 = rateMoment rates v 1 := by
    have hzero : (∑ i, a i * rates i ^ (1 : ℕ)) = 0 := by
      simpa only [rateMoment_eq_sum] using hmoment ⟨1, by decide⟩
    rw [rateMoment_eq_sum, rateMoment_eq_sum, ← sub_eq_zero, hsum_diff, hzero, zero_div]
  refine ⟨w, v, ?_, ?_, ?_, ?_, hsum_w, hsum_v, hmean, ?_⟩
  · obtain ⟨i, hi⟩ := hcoeff
    intro heq
    have h := hdiff i
    rw [heq, sub_self] at h
    exact (div_ne_zero hi hmass_pos.ne') h.symm
  · intro i
    refine ⟨div_nonneg (le_max_right _ _) hmass_pos.le,
      div_nonneg (le_max_right _ _) hmass_pos.le, ?_⟩
    rcases le_total 0 (a i) with hi | hi
    · simp [v, max_eq_right (neg_nonpos.mpr hi)]
    · simp [w, max_eq_right hi]
  · rw [hw]; omega
  · rw [hv]; omega
  · intro s hs
    have hl : tiltedRateMoment rates w 0 s = tiltedRateMoment rates v 0 s := by
      have hzero : (∑ i, a i * Real.exp (-(s * rates i))) = 0 := by
        simpa only [tiltedRateMoment, pow_zero, mul_one] using hlaplace s hs
      simp only [tiltedRateMoment, pow_zero, mul_one]
      rw [← sub_eq_zero, hsum_diff, hzero, zero_div]
    simp only [rateProfile_eq_laplace, hl, hmean, rateMoment_eq_sum, pow_zero, mul_one,
      hsum_w, hsum_v]

#print axioms rateProfile_identifies_weights
#print axioms rateProfile_query_count_sharp

end D5.S3.Analytic.PetzDyadicEscapeIdentification
