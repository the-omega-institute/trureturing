/- GID: D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The full real minimum-mass slope strictly increases with the number of labels. -/

import D5.S3.Arith.FibonacciAtomic.CarryGraphCriticalAttainment
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.OptimalLawStrictSlope

open scoped BigOperators
open CarryGraphEmbedding
open CarryGraphCriticalAttainment (alpha)
open DyadicSupportLines (cost)

/-- The full real optimal ratio has its single- and two-label endpoint values,
and strictly increases at every subsequent label count. -/
theorem result : alpha 1 = 0 ∧ alpha 2 = 2 ∧
    ∀ m : ℕ, 3 ≤ m → alpha (m - 1) < alpha m := by
  classical
  have law_data (n : ℕ) (hn : 2 ≤ n) (p : Fin n → ℝ)
      (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) (k : Fin n)
      (hk : ∀ i, p k ≤ p i) :
      (∀ d, 0 ≤ DyadicSupportLines.residual p d) ∧
      Summable (fun d => DyadicSupportLines.residual p d / (2 : ℝ) ^ d) ∧ 1 ≤ cost p := by
    obtain ⟨γ, hγ, hr, _, _, _, _⟩ := (CarryGraphEmbedding.result n hn).2.2.2 p hp hs k hk
    have bounds (d : ℕ) : 0 ≤ DyadicSupportLines.residual p d ∧ DyadicSupportLines.residual p d ≤ n := by
      have H := (hγ.2 d).1.1
      dsimp [IsState] at H
      rw [← hr d]
      exact ⟨by exact_mod_cast H.1, by exact_mod_cast (show (γ.state d).r ≤ n by omega)⟩
    have nonneg (d : ℕ) : 0 ≤ DyadicSupportLines.residual p d / (2 : ℝ) ^ d :=
      div_nonneg (bounds d).1 (by positivity)
    have summable : Summable (fun d => DyadicSupportLines.residual p d / (2 : ℝ) ^ d) := by
      apply Summable.of_nonneg_of_le nonneg
        (fun d => div_le_div_of_nonneg_right (bounds d).2 (by positivity))
      simpa [div_pow, div_eq_mul_inv] using
        (summable_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).mul_left (n : ℝ)
    refine ⟨fun d => (bounds d).1, summable, ?_⟩
    have H := summable.sum_le_tsum ({0} : Finset ℕ) (fun d _ => nonneg d)
    have root_residual : DyadicSupportLines.residual p 0 = 1 := by
      rw [← hr 0, hγ.1]
      norm_num [root]
    simpa [Finset.sum_singleton, root_residual, cost] using H
  have alpha_le (n : ℕ) (hn : 2 ≤ n) (p : Fin n → ℝ)
      (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) (k : Fin n)
      (hk : ∀ i, p k ≤ p i) : alpha n ≤ cost p / p k := by
    apply csInf_le (show BddBelow {y : ℝ | ∃ (q : Fin n → ℝ) (j : Fin n),
      (∀ i, 0 < q i) ∧ (∑ i, q i) = 1 ∧ (∀ i, q j ≤ q i) ∧ y = cost q / q j} from ?_)
      ⟨p, k, hp, hs, hk, rfl⟩
    refine ⟨0, ?_⟩
    rintro y ⟨q, j, hq, hsum, hj, rfl⟩
    exact div_nonneg (by linarith [(law_data n hn q hq hsum j hj).2.2]) (hq j).le
  have single_cost : cost (fun _ : Fin 1 => (1 : ℝ)) = 0 := by
    have zeros (d : ℕ) : DyadicSupportLines.residual (fun _ : Fin 1 => (1 : ℝ)) d / (2 : ℝ) ^ d = 0 := by
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
    · have H := alpha_le 2 (by omega) (fun _ => 1 / 2) (by norm_num)
        (by norm_num) 0 (by simp)
      rw [uniform_cost] at H
      norm_num at H
      exact H
    · refine le_csInf (show ({y : ℝ | ∃ (p : Fin 2 → ℝ) (k : Fin 2),
        (∀ i, 0 < p i) ∧ (∑ i, p i) = 1 ∧ (∀ i, p k ≤ p i) ∧ y = cost p / p k}).Nonempty from
        ⟨2, fun _ => 1 / 2, 0, by norm_num, by norm_num, by simp,
          by simp only [uniform_cost]; norm_num⟩) ?_
      rintro y ⟨p, k, hp, hs, hk, rfl⟩
      have H := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 2))) (fun i _ => hk i)
      have half : p k ≤ 1 / 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hs] at H
        norm_num only [Nat.cast_ofNat] at H
        linarith
      apply (le_div_iff₀ (hp k)).mpr
      linarith [(law_data 2 (by omega) p hp hs k hk).2.2]
  refine ⟨one, two, ?_⟩
  intro m hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hn : 2 ≤ n := by omega
  simp only [Nat.add_sub_cancel]
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  haveI : Nonempty (Fin (n + 1)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨V, f, H⟩ := CarryGraphCriticalAttainment.result (n + 1) (by omega)
  rcases H with ⟨_, _, _, _, _, H⟩
  dsimp only at H
  let γ := CarryGraphCriticalAttainment.policyPath (n + 1) (f (alpha (n + 1)))
    ⟨root (n + 1), by dsimp [IsState, root]; omega⟩
  let p : Fin (n + 1) → ℝ := fun i => Real.ofDigits (CarryGraphRealization.labelDigit γ i)
  rcases H with ⟨ht, hp, hs, hmin, _, _, _, _, hcost⟩
  change (∀ i, 0 < p i) at hp
  change ∑ i, p i = 1 at hs
  change sInf (Set.range p) = anchorValue γ at hmin
  change cost p = alpha (n + 1) * anchorValue γ at hcost
  obtain ⟨k, hk0⟩ := (Set.range_nonempty p).csInf_mem (Set.finite_range p)
  have hk : ∀ i, p k ≤ p i := by
    intro i
    rw [hk0]
    exact csInf_le (Set.finite_range p).bddBelow ⟨i, rfl⟩
  have optimum : cost p / p k = alpha (n + 1) := by
    rw [hk0, hmin, hcost, mul_div_cancel_right₀ _ (ne_of_gt ht)]
  have psmall : p k < 1 := by
    have H := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hk i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hs] at H
    norm_num only [Nat.cast_add, Nat.cast_one] at H
    have N : (3 : ℝ) ≤ n + 1 := by exact_mod_cast hm
    nlinarith [hp k]
  have pd := law_data (n + 1) (by omega) p hp hs k hk
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
    have qd := law_data n hn q hq hsum j hj'
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
        div_le_div_of_nonneg_left (by linarith [qd.2.2]) (hp k) (hlow j)
      exact H.trans_lt (div_lt_div_of_pos_right strict_cost (hp k))
    rw [← optimum]
    exact (alpha_le n hn q hq hsum j hj').trans_lt ratio
  · let l : Fin n := ⟨0, by omega⟩
    let q : Fin n → ℝ := fun i => p (k.succAbove i) + if i = l then p k else 0
    rcases merged l with ⟨hq, hsum, hlow, hres, _⟩
    obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ q Finset.univ_nonempty
    have hj' : ∀ i, q j ≤ q i := fun i => hj i (Finset.mem_univ i)
    have qd := law_data n hn q hq hsum j hj'
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
        _ < cost p / p k := div_lt_div_of_pos_left (by linarith [pd.2.2]) (hp k) strict_minimum
    rw [← optimum]
    exact (alpha_le n hn q hq hsum j hj').trans_lt ratio

end D5.S3.Arith.FibonacciAtomic.OptimalLawStrictSlope
