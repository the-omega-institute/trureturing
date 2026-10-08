/- GID: D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The full real minimum-mass slope strictly increases with the number of labels. -/

import D5.S3.Arith.FibonacciAtomic.DyadicSupportLines
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.OptimalLawStrictSlope

open scoped BigOperators
open Filter Topology
open DyadicSupportLines (cost)

/-- The infimum ranges over all strictly positive normalized real laws and every
index at which the least mass is attained. -/
noncomputable def alpha (m : ℕ) : ℝ :=
  sInf {y : ℝ | ∃ (p : Fin m → ℝ) (k : Fin m),
    (∀ i, 0 < p i) ∧ (∑ i, p i) = 1 ∧ (∀ i, p k ≤ p i) ∧
      y = cost p / p k}

/-- The normalized floor residuals are nonnegative, bounded, and summable. -/
theorem law_data (m : ℕ) (p : Fin m → ℝ) (hs : ∑ i, p i = 1) :
    (∀ d, 0 ≤ DyadicSupportLines.residual p d ∧
      DyadicSupportLines.residual p d ≤ m) ∧
    Summable (fun d => DyadicSupportLines.residual p d / (2 : ℝ) ^ d) ∧ 0 ≤ cost p := by
  have bounds (d : ℕ) : 0 ≤ DyadicSupportLines.residual p d ∧
      DyadicSupportLines.residual p d ≤ m := by
    have lo := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => Int.floor_le ((2 : ℝ) ^ d * p i))
    have hi := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => (Int.lt_floor_add_one ((2 : ℝ) ^ d * p i)).le)
    simp only [← Finset.mul_sum, hs, mul_one, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at lo hi
    simp only [DyadicSupportLines.residual, Int.cast_sum]
    constructor <;> linarith
  have nn (d : ℕ) : 0 ≤ DyadicSupportLines.residual p d / (2 : ℝ) ^ d :=
    div_nonneg (bounds d).1 (by positivity)
  have sm : Summable (fun d => DyadicSupportLines.residual p d / (2 : ℝ) ^ d) :=
    Summable.of_nonneg_of_le nn
      (fun d => div_le_div_of_nonneg_right (bounds d).2 (by positivity)) (by
        simpa [div_pow, div_eq_mul_inv] using
          (summable_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).mul_left (m : ℝ))
  exact ⟨bounds, sm, tsum_nonneg nn⟩

/-- Every strictly positive normalized law with at least two labels costs at least one bit. -/
theorem cost_ge_one (m : ℕ) (hm : 2 ≤ m) (p : Fin m → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) : 1 ≤ cost p := by
  classical
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  have floors (i : Fin m) : ⌊p i⌋ = 0 := by
    apply Int.floor_eq_zero_iff.mpr
    refine ⟨(hp i).le, ?_⟩
    obtain ⟨j, hj⟩ := exists_ne i
    have h := Finset.add_le_sum (s := Finset.univ) (fun a _ => (hp a).le)
      (by simp : i ∈ Finset.univ) (by simp : j ∈ Finset.univ) (Ne.symm hj)
    rw [hs] at h
    linarith [hp j]
  have data := law_data m p hs
  have h := data.2.1.sum_le_tsum ({0} : Finset ℕ)
    (fun d _ => div_nonneg (data.1 d).1 (by positivity))
  simpa [cost, DyadicSupportLines.residual, floors] using h

/-- Each admissible law bounds the full real infimum from above. -/
theorem alpha_le (m : ℕ) (p : Fin m → ℝ) (hp : ∀ i, 0 < p i)
    (hs : ∑ i, p i = 1) (k : Fin m) (hk : ∀ i, p k ≤ p i) :
    alpha m ≤ cost p / p k := by
  apply csInf_le (show BddBelow {y : ℝ | ∃ (q : Fin m → ℝ) (j : Fin m),
    (∀ i, 0 < q i) ∧ (∑ i, q i) = 1 ∧ (∀ i, q j ≤ q i) ∧ y = cost q / q j} from ?_)
    ⟨p, k, hp, hs, hk, rfl⟩
  refine ⟨0, ?_⟩
  rintro y ⟨q, j, hq, hsum, hj, rfl⟩
  exact div_nonneg (law_data m q hsum).2.2 (hq j).le

/-- The label count is a lower bound for the optimal ratio on every positive
multi-label real simplex. -/
theorem alpha_ge_labels (m : ℕ) (hm : 2 ≤ m) : (m : ℝ) ≤ alpha m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  let u : Fin m → ℝ := fun _ => 1 / m
  let k : Fin m := ⟨0, by omega⟩
  have upos : ∀ i, 0 < u i := fun _ => one_div_pos.mpr hmpos
  have usum : ∑ i, u i = 1 := by
    simp only [u, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel hmpos.ne'
  apply le_csInf (show ({y : ℝ | ∃ (p : Fin m → ℝ) (j : Fin m),
    (∀ i, 0 < p i) ∧ (∑ i, p i) = 1 ∧ (∀ i, p j ≤ p i) ∧
      y = cost p / p j}).Nonempty from
    ⟨cost u / u k, u, k, upos, usum, fun _ => le_rfl, rfl⟩)
  rintro y ⟨p, j, hp, hs, hj, rfl⟩
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hj i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hs] at h
  exact (le_div_iff₀ (hp j)).mpr (by nlinarith [cost_ge_one m hm p hp hs])

/-- On positive normalized real laws, the dyadic cost-to-coordinate ratio is
lower semicontinuous, including at terminating binary coordinates. -/
theorem ratio_lower_semicontinuous (m : ℕ) (k : Fin m) :
    LowerSemicontinuousOn (fun p : Fin m → ℝ => cost p / p k)
      {p | (∀ i, 0 < p i) ∧ (∑ i, p i) = 1} := by
  classical
  intro p hp y hy
  have sm := (law_data m p hp.2).2.1
  have limit : Filter.Tendsto
      (fun n : ℕ => (∑ d ∈ Finset.range n, DyadicSupportLines.residual p d / (2 : ℝ) ^ d) / p k)
      Filter.atTop (nhds (cost p / p k)) := by
    exact sm.hasSum.tendsto_sum_nat.div_const (p k)
  obtain ⟨n, hs⟩ := (limit.eventually (Ioi_mem_nhds hy)).exists
  let s := Finset.range n
  let c := ∑ d ∈ s, DyadicSupportLines.residual p d / (2 : ℝ) ^ d
  have floor_event : ∀ᶠ q : Fin m → ℝ in nhds p, ∀ d ∈ s, ∀ i,
      ⌊(2 : ℝ) ^ d * q i⌋ ≤ ⌊(2 : ℝ) ^ d * p i⌋ := by
    rw [Filter.eventually_all_finset]
    intro d hd
    rw [Filter.eventually_all]
    intro i
    have h := ((continuous_const.mul (continuous_apply i)).tendsto p).eventually
      (Iio_mem_nhds (Int.lt_floor_add_one ((2 : ℝ) ^ d * p i)))
    filter_upwards [h] with q hq
    exact Int.lt_add_one_iff.mp (Int.floor_lt.mpr (by simpa using hq))
  have cont : ContinuousAt (fun q : Fin m → ℝ => c / q k) p :=
    continuousAt_const.div (continuous_apply k).continuousAt (ne_of_gt (hp.1 k))
  have ev := cont.tendsto.eventually (Ioi_mem_nhds hs)
  filter_upwards [floor_event.filter_mono nhdsWithin_le_nhds,
    ev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hf hq hmem
  have lower : c ≤ ∑ d ∈ s, DyadicSupportLines.residual q d / (2 : ℝ) ^ d := by
    apply Finset.sum_le_sum
    intro d hd
    apply div_le_div_of_nonneg_right _ (by positivity)
    simp only [DyadicSupportLines.residual, Int.cast_sum]
    apply sub_le_sub_left
    exact Finset.sum_le_sum fun i _ => Int.cast_le.mpr (hf d hd i)
  have data := law_data m q hmem.2
  exact hq.trans_le ((div_le_div_of_nonneg_right lower (hmem.1 k).le).trans
    (div_le_div_of_nonneg_right (data.2.1.sum_le_tsum s
      (fun d _ => div_nonneg (data.1 d).1 (by positivity))) (hmem.1 k).le))

/-- The full positive real optimization domain has an attaining law, without any
rationality, computability, or depth restriction. -/
theorem attained (m : ℕ) (hm : 2 ≤ m) :
    ∃ (p : Fin m → ℝ) (k : Fin m),
      (∀ i, 0 < p i) ∧ (∑ i, p i) = 1 ∧ (∀ i, p k ≤ p i) ∧
        cost p / p k = alpha m := by
  classical
  let k : Fin m := ⟨0, by omega⟩
  let u : Fin m → ℝ := fun _ => 1 / m
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have upos : ∀ i, 0 < u i := fun _ => one_div_pos.mpr hmpos
  have usum : ∑ i, u i = 1 := by
    simp only [u, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel hmpos.ne'
  let R := cost u / u k
  have Rpos : 0 < R := div_pos (lt_of_lt_of_le zero_lt_one (cost_ge_one m hm u upos usum)) (upos k)
  let a := 1 / (R + 1)
  have apos : 0 < a := one_div_pos.mpr (by linarith)
  have au : a ≤ u k := by
    apply (div_le_iff₀ (by linarith : 0 < R + 1)).mpr
    have r := (div_eq_iff (ne_of_gt (upos k))).mp (show R = cost u / u k from rfl)
    nlinarith [cost_ge_one m hm u upos usum, upos k]
  have uone : u k ≤ 1 := by
    dsimp [u]
    exact (div_le_one hmpos).mpr (by exact_mod_cast (show 1 ≤ m by omega))
  let K : Set (Fin m → ℝ) := Set.Icc (fun _ => a) (fun _ => 1) ∩
    {p | (∑ i, p i) = 1 ∧ ∀ i, p k ≤ p i}
  have closed : IsClosed {p : Fin m → ℝ | (∑ i, p i) = 1 ∧ ∀ i, p k ≤ p i} :=
    (isClosed_eq (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const).inter
      (by
        change IsClosed {p : Fin m → ℝ | ∀ i, p k ≤ p i}
        rw [Set.ofPred_forall]
        exact isClosed_iInter fun i : Fin m => isClosed_le
          (continuous_apply k : Continuous (fun p : Fin m → ℝ => p k))
          (continuous_apply i : Continuous (fun p : Fin m → ℝ => p i)))
  have compact : IsCompact K := isCompact_Icc.inter_right closed
  have uK : u ∈ K := ⟨⟨fun _ => au, fun _ => uone⟩, usum, fun _ => le_rfl⟩
  have positive (p : Fin m → ℝ) (hp : p ∈ K) : ∀ i, 0 < p i :=
    fun i => apos.trans_le (hp.1.1 i)
  obtain ⟨p, hp, hmin⟩ := (ratio_lower_semicontinuous m k).mono
    (show K ⊆ {p | (∀ i, 0 < p i) ∧ (∑ i, p i) = 1} from
      fun p hp => ⟨positive p hp, hp.2.1⟩) |>.exists_isMinOn ⟨u, uK⟩ compact
  have below (q : Fin m → ℝ) (j : Fin m) (hq : ∀ i, 0 < q i)
      (hs : ∑ i, q i = 1) (hj : ∀ i, q j ≤ q i) : cost p / p k ≤ cost q / q j := by
    by_cases ha : a ≤ q j
    · let e := Equiv.swap k j
      let v : Fin m → ℝ := fun i => q (e i)
      have vk : v k = q j := by simp [v, e]
      have vs : ∑ i, v i = 1 := (Equiv.sum_comp e q).trans hs
      have vlo : ∀ i, a ≤ v i := fun i => ha.trans (hj (e i))
      have vhi : ∀ i, v i ≤ 1 := by
        intro i
        have h := Finset.single_le_sum (s := Finset.univ) (fun l _ => (hq (e l)).le)
          (Finset.mem_univ i)
        change v i ≤ ∑ l, v l at h
        exact h.trans_eq vs
      have vc : cost v = cost q := by
        unfold cost
        congr 1
        funext d
        simp only [DyadicSupportLines.residual, v]
        rw [Equiv.sum_comp e (fun i => ⌊(2 : ℝ) ^ d * q i⌋)]
      have vK : v ∈ K := ⟨⟨vlo, vhi⟩, vs, fun i => by rw [vk]; exact hj (e i)⟩
      have h : cost p / p k ≤ cost v / v k := hmin vK
      simpa only [vc, vk] using h
    · have small : q j < a := lt_of_not_ge ha
      have H : R + 1 < cost q / q j := by
        apply (lt_div_iff₀ (hq j)).mpr
        have hsmall := (lt_div_iff₀ (by linarith : 0 < R + 1)).mp small
        nlinarith [cost_ge_one m hm q hq hs]
      exact (hmin uK).trans (by change R ≤ cost q / q j; linarith)
  refine ⟨p, k, positive p hp, hp.2.1, hp.2.2, le_antisymm ?_ ?_⟩
  · apply le_csInf (show ({y : ℝ | ∃ (q : Fin m → ℝ) (j : Fin m),
      (∀ i, 0 < q i) ∧ (∑ i, q i) = 1 ∧ (∀ i, q j ≤ q i) ∧
        y = cost q / q j}).Nonempty from
      ⟨cost u / u k, u, k, upos, usum, fun _ => le_rfl, rfl⟩)
    rintro y ⟨q, j, hq, hs, hj, rfl⟩
    exact below q j hq hs hj
  · exact alpha_le m p (positive p hp) hp.2.1 k hp.2.2

/-- The full real optimal ratio has its single- and two-label endpoint values,
and strictly increases at every subsequent label count. -/
theorem result : alpha 1 = 0 ∧ alpha 2 = 2 ∧
    ∀ m : ℕ, 3 ≤ m → alpha (m - 1) < alpha m := by
  classical
  have single_cost : cost (fun _ : Fin 1 => (1 : ℝ)) = 0 := by
    have zeros (d : ℕ) :
        DyadicSupportLines.residual (fun _ : Fin 1 => (1 : ℝ)) d / (2 : ℝ) ^ d = 0 := by
      have integer_pow : ⌊(2 : ℝ) ^ d⌋ = (2 : ℤ) ^ d := by
        exact_mod_cast (Int.floor_intCast ((2 : ℤ) ^ d))
      simp [DyadicSupportLines.residual, integer_pow]
    simp [cost, zeros]
  have one : alpha 1 = 0 := by
    have ratios : {y : ℝ | ∃ (p : Fin 1 → ℝ) (k : Fin 1),
      (∀ i, 0 < p i) ∧ (∑ i, p i) = 1 ∧ (∀ i, p k ≤ p i) ∧ y = cost p / p k} = {0} := by
      ext y
      constructor
      · rintro ⟨p, k, hp, hs, hk, rfl⟩
        have H : p = fun _ => 1 := by
          funext i
          simpa only [Fin.sum_univ_one, Fin.eq_zero i] using hs
        simp [H, single_cost]
      · rintro rfl
        exact ⟨fun _ => 1, 0, by norm_num, by simp, by simp, by simp [single_cost]⟩
    unfold alpha
    rw [ratios, csInf_singleton]
  have uniform_cost : cost (fun _ : Fin 2 => (1 / 2 : ℝ)) = 1 := by
    have terms (d : ℕ) : DyadicSupportLines.residual (fun _ : Fin 2 => (1 / 2 : ℝ)) d /
        (2 : ℝ) ^ d = if d = 0 then 1 else 0 := by
      cases d with
      | zero => norm_num [DyadicSupportLines.residual]
      | succ d =>
        have floorpow : ⌊(2 : ℝ) ^ d⌋ = (2 : ℤ) ^ d := by
          exact_mod_cast (Int.floor_intCast ((2 : ℤ) ^ d))
        simp [DyadicSupportLines.residual, floorpow, pow_succ]
        ring
    simp only [cost, terms]
    simp
  have two : alpha 2 = 2 := by
    apply le_antisymm
    · have H := alpha_le 2 (fun _ => 1 / 2) (by norm_num)
        (by norm_num) 0 (by simp)
      rw [uniform_cost] at H
      norm_num at H
      exact H
    · exact_mod_cast alpha_ge_labels 2 (by omega)
  refine ⟨one, two, ?_⟩
  intro m hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hn : 2 ≤ n := by omega
  simp only [Nat.add_sub_cancel]
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have : Nonempty (Fin (n + 1)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨p, k, hp, hs, hk, optimum⟩ := attained (n + 1) (by omega)
  have psmall : p k < 1 := by
    have H := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hk i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hs] at H
    norm_num only [Nat.cast_add, Nat.cast_one] at H
    have N : (3 : ℝ) ≤ n + 1 := by exact_mod_cast hm
    nlinarith [hp k]
  have pd := law_data (n + 1) p hs
  have merged (l : Fin n) :
      let q : Fin n → ℝ := fun i => p (k.succAbove i) + if i = l then p k else 0
      (∀ i, 0 < q i) ∧ (∑ i, q i) = 1 ∧
      (∀ i, p k ≤ q i) ∧
      (∀ d, DyadicSupportLines.residual q d ≤ DyadicSupportLines.residual p d) ∧
      (∀ d, DyadicSupportLines.residual q d = DyadicSupportLines.residual p d -
        (↑(⌊(2 : ℝ) ^ d * (p k + p (k.succAbove l))⌋ -
          ⌊(2 : ℝ) ^ d * p k⌋ - ⌊(2 : ℝ) ^ d * p (k.succAbove l)⌋) : ℝ)) := by
    dsimp only
    let q : Fin n → ℝ := fun i => p (k.succAbove i) + if i = l then p k else 0
    have positive : ∀ i, 0 < q i := by
      intro i
      dsimp [q]
      split_ifs <;> linarith [hp (k.succAbove i), hp k]
    have total : ∑ i, q i = 1 := by
      simp only [q, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have H := Fin.sum_univ_succAbove p k
      linarith
    have lower : ∀ i, p k ≤ q i := by
      intro i
      dsimp [q]
      split_ifs <;> linarith [hk (k.succAbove i), hp k]
    have floor_terms (d : ℕ) (i : Fin n) : ⌊(2 : ℝ) ^ d * q i⌋ =
        ⌊(2 : ℝ) ^ d * p (k.succAbove i)⌋ +
        if i = l then ⌊(2 : ℝ) ^ d * (p k + p (k.succAbove l))⌋ -
          ⌊(2 : ℝ) ^ d * p (k.succAbove l)⌋ else 0 := by
      by_cases h : i = l
      · subst i
        simp only [q, ite_true]
        rw [add_comm (p (k.succAbove l)) (p k)]
        omega
      · simp [q, h]
    have floor_sum (d : ℕ) : (∑ i, ⌊(2 : ℝ) ^ d * q i⌋) =
        (∑ i, ⌊(2 : ℝ) ^ d * p i⌋) - ⌊(2 : ℝ) ^ d * p k⌋ -
        ⌊(2 : ℝ) ^ d * p (k.succAbove l)⌋ +
        ⌊(2 : ℝ) ^ d * (p k + p (k.succAbove l))⌋ := by
      simp_rw [floor_terms]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have H := Fin.sum_univ_succAbove (fun i => ⌊(2 : ℝ) ^ d * p i⌋) k
      omega
    have residual_eq (d : ℕ) : DyadicSupportLines.residual q d = DyadicSupportLines.residual p d -
        (↑(⌊(2 : ℝ) ^ d * (p k + p (k.succAbove l))⌋ -
          ⌊(2 : ℝ) ^ d * p k⌋ - ⌊(2 : ℝ) ^ d * p (k.succAbove l)⌋) : ℝ) := by
      simp only [DyadicSupportLines.residual, floor_sum]
      push_cast
      ring
    refine ⟨positive, total, lower, ?_, residual_eq⟩
    intro d
    rw [residual_eq]
    have H := Int.le_floor_add ((2 : ℝ) ^ d * p k) ((2 : ℝ) ^ d * p (k.succAbove l))
    rw [← mul_add] at H
    have H' : (0 : ℝ) ≤ ↑(⌊(2 : ℝ) ^ d * (p k + p (k.succAbove l))⌋ -
        ⌊(2 : ℝ) ^ d * p k⌋ - ⌊(2 : ℝ) ^ d * p (k.succAbove l)⌋) := by
      have HI : (0 : ℤ) ≤ ⌊(2 : ℝ) ^ d * (p k + p (k.succAbove l))⌋ -
          ⌊(2 : ℝ) ^ d * p k⌋ - ⌊(2 : ℝ) ^ d * p (k.succAbove l)⌋ := by omega
      have HC : ((0 : ℤ) : ℝ) ≤ ↑(⌊(2 : ℝ) ^ d * (p k + p (k.succAbove l))⌋ -
          ⌊(2 : ℝ) ^ d * p k⌋ - ⌊(2 : ℝ) ^ d * p (k.succAbove l)⌋) := Int.cast_le.mpr HI
      simpa only [Int.cast_zero] using HC
    linarith
  by_cases tied : ∃ l : Fin n, p (k.succAbove l) = p k
  · obtain ⟨l, hl⟩ := tied
    let q : Fin n → ℝ := fun i => p (k.succAbove i) + if i = l then p k else 0
    rcases merged l with ⟨hq, hsum, hlow, hres, heq⟩
    obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ q Finset.univ_nonempty
    have hj' : ∀ i, q j ≤ q i := fun i => hj i (Finset.mem_univ i)
    have qd := law_data n q hsum
    have crossing : ∃ d : ℕ, 1 ≤ (2 : ℝ) ^ d * p k := by
      obtain ⟨d, hd⟩ := pow_unbounded_of_one_lt (1 / p k) (by norm_num : (1 : ℝ) < 2)
      exact ⟨d, (div_lt_iff₀ (hp k)).mp hd |>.le⟩
    let d := Nat.find crossing
    have hd : 1 ≤ (2 : ℝ) ^ d * p k := Nat.find_spec crossing
    have dpos : 0 < d := by
      by_contra H
      have dz : d = 0 := by omega
      rw [dz, pow_zero, one_mul] at hd
      linarith
    obtain ⟨e, de⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have he : (2 : ℝ) ^ e * p k < 1 :=
      lt_of_not_ge (Nat.find_min crossing (by dsimp [d] at *; omega))
    have floor_zero : ⌊(2 : ℝ) ^ e * p k⌋ = 0 :=
      Int.floor_eq_zero_iff.mpr ⟨mul_nonneg (by positivity) (hp k).le, he⟩
    have carry : (1 : ℤ) ≤ ⌊(2 : ℝ) ^ e * (p k + p (k.succAbove l))⌋ := by
      rw [Int.le_floor]
      rw [de, pow_succ] at hd
      rw [hl]
      norm_num only [Int.cast_one]
      nlinarith
    have strict_residual : DyadicSupportLines.residual q e < DyadicSupportLines.residual p e := by
      rw [heq e, hl, floor_zero]
      have H : (1 : ℝ) ≤ ↑⌊(2 : ℝ) ^ e * (p k + p k)⌋ := by
        have HC : ((1 : ℤ) : ℝ) ≤ ↑⌊(2 : ℝ) ^ e * (p k + p k)⌋ :=
          Int.cast_le.mpr (by simpa only [hl] using carry)
        simpa only [Int.cast_one] using HC
      push_cast
      linarith
    have strict_cost : cost q < cost p :=
      qd.2.1.tsum_lt_tsum (fun d => div_le_div_of_nonneg_right (hres d) (by positivity))
        (div_lt_div_of_pos_right strict_residual (by positivity)) pd.2.1
    have ratio : cost q / q j < cost p / p k := by
      have H : cost q / q j ≤ cost q / p k :=
        div_le_div_of_nonneg_left (by linarith [cost_ge_one n hn q hq hsum]) (hp k) (hlow j)
      exact H.trans_lt (div_lt_div_of_pos_right strict_cost (hp k))
    rw [← optimum]
    exact (alpha_le n q hq hsum j hj').trans_lt ratio
  · let l : Fin n := ⟨0, by omega⟩
    let q : Fin n → ℝ := fun i => p (k.succAbove i) + if i = l then p k else 0
    rcases merged l with ⟨hq, hsum, hlow, hres, _⟩
    obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ q Finset.univ_nonempty
    have hj' : ∀ i, q j ≤ q i := fun i => hj i (Finset.mem_univ i)
    have qd := law_data n q hsum
    have strict_minimum : p k < q j := by
      have H : p k < p (k.succAbove j) :=
        lt_of_le_of_ne (hk (k.succAbove j)) (fun h => tied ⟨j, h.symm⟩)
      dsimp [q]
      split_ifs <;> linarith [hp k]
    have cost_le : cost q ≤ cost p :=
      qd.2.1.tsum_le_tsum (fun d => div_le_div_of_nonneg_right (hres d) (by positivity)) pd.2.1
    have ratio : cost q / q j < cost p / p k := by
      calc
        _ ≤ cost p / q j := div_le_div_of_nonneg_right cost_le (hq j).le
        _ < cost p / p k := div_lt_div_of_pos_left
          (by linarith [cost_ge_one (n + 1) (by omega) p hp hs]) (hp k) strict_minimum
    rw [← optimum]
    exact (alpha_le n q hq hsum j hj').trans_lt ratio

end D5.S3.Arith.FibonacciAtomic.OptimalLawStrictSlope
