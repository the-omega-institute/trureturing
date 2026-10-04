/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnbounded
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelUnbounded
   mirror-E: none(waiver:external-metallic-hankel-unboundedness)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Normal cofactor growth and finite strip comparison prove metallic unboundedness. -/

import Mathlib.Algebra.Ring.GeomSum
import D5.S3.Combinatorics.MetallicHankel.MetallicHankel
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedDefs
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedCofactor
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedGolden
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedTransfer
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedGrowth
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedStrip

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnbounded

open PowerSeries Finset MetallicHankelDefs MetallicHankelData
open MetallicHankelTransitions MetallicHankelDeterminants
open MetallicHankelUnboundedCofactor MetallicHankelUnboundedGolden
open MetallicHankelUnboundedTransfer MetallicHankelUnboundedGrowth
open TrivSqZeroExt

set_option maxHeartbeats 4000000 in
/-- Conjecture E(2), including the separate golden cycle. -/
theorem result : MetallicHankelUnboundedDefs.claim := by
  classical
  intro n hn
  let a := max n 2
  have ha : 2 ≤ a := le_max_right _ _
  have an (h : n ≠ 1) : a = n := by dsimp [a]; omega
  obtain ⟨length_eq, valid_cycle, chain, weight, word, denominator⟩ := cycle_data a ha
  let L₀ := (cycle a).length
  have L₀pos : 0 < L₀ := by dsimp [L₀]; rw [length_eq]; omega
  let state : ℕ → TailState := Nat.rec .v₂ (fun _ z => nextState a z)
  have state_zero : state 0 = .v₂ := rfl
  have state_step (p : ℕ) : state (p + 1) = nextState a (state p) := rfl
  have state_segment : ∀ p, p ≤ L₀ →
      state p = (cycle a ++ [TailState.v₂]).getD p .v₂ := by
    intro p
    induction p with
    | zero => simp [state, cycle]
    | succ p ih =>
      intro hp
      have hlt : p < (cycle a ++ [TailState.v₂]).length := by simp [L₀] at *; omega
      have hlt' : p + 1 < (cycle a ++ [TailState.v₂]).length := by simp [L₀] at *; omega
      have hc := chain.getElem p hlt'
      rw [List.getElem_eq_getD TailState.v₂, List.getElem_eq_getD TailState.v₂] at hc
      rw [state_step, ih (by omega)]
      exact hc
  have state_end : state L₀ = .v₂ := by
    rw [state_segment L₀ (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by exact le_rfl)]
    simp [L₀]
  have state_period : ∀ p, state (p + L₀) = state p := by
    intro p
    induction p with
    | zero => simpa [state_zero] using state_end
    | succ p ih =>
      rw [show p + 1 + L₀ = (p + L₀) + 1 by omega, state_step, state_step, ih]
  have state_at (i : ℕ) (hi : i < L₀) : state i = (cycle a)[i]'hi := by
    rw [state_segment i (by omega), ← List.getElem_eq_getD TailState.v₂]
    · exact List.getElem_append_left hi
    · simp only [List.length_append, List.length_singleton]
      exact Nat.lt_add_right 1 hi
  have state_mod : ∀ p, state p = state (p % L₀) := by
    intro p
    induction p using Nat.strong_induction_on with
    | h p ih =>
      by_cases hp : p < L₀
      · rw [Nat.mod_eq_of_lt hp]
      · have hl : L₀ ≤ p := by omega
        rw [← Nat.sub_add_cancel hl, state_period]
        rw [ih (p - L₀) (by omega), Nat.sub_add_cancel hl, ← Nat.mod_eq_sub_mod hl]
  have valid (p : ℕ) : validState a (state p) := by
    rw [state_mod, state_at _ (Nat.mod_lt p L₀pos)]
    exact valid_cycle _ (List.getElem_mem _)
  let L := if n = 1 then 3 else L₀
  let P := if n = 1 then 4 else 2 * n * (n + 1)
  have Lpos' : 0 < L := by dsimp [L]; split_ifs <;> omega
  let k (p : ℕ) := if n = 1 then (if p % 3 = 2 then 1 else 0)
    else (fractionData a (state p)).1
  let b (p : ℕ) : ℤ := if n = 1 then (if p % 3 = 1 then 1 else -1)
    else (fractionData a (state p)).2.1
  let v (p : ℕ) : ℤ := if p = 0 then 1 else b p
  let D (p : ℕ) : PowerSeries ℤ := if n = 1 then
    (if p % 3 = 2 then 1 + X - X ^ 2 else 1 + X)
    else (fractionData a (state p)).2.2
  let s (p : ℕ) := ∑ i ∈ range p, (k i + 1)
  let h (p : ℕ) : ℤ := -∏ i ∈ range (p + 1), b i
  let numerator (p : ℕ) := C (v (p + 1)) * X ^ (k p + k (p + 1) + 2)
  let qpair : ℕ → PowerSeries ℤ × PowerSeries ℤ :=
    Nat.rec (1, D 0) (fun p z => (z.2, D (p + 1) * z.2 - numerator p * z.1))
  let npair : ℕ → PowerSeries ℤ × PowerSeries ℤ :=
    Nat.rec (0, C (v 0) * X ^ k 0)
      (fun p z => (z.2, D (p + 1) * z.2 - numerator p * z.1))
  let Q (p : ℕ) := (qpair p).1
  let N (p : ℕ) := (npair p).1
  have s_zero : s 0 = 0 := by simp [s]
  have s_step (p : ℕ) : s (p + 1) = s p + k p + 1 := by
    change (∑ i ∈ range (p + 1), (k i + 1)) = _
    rw [sum_range_succ]
    exact Nat.add_assoc _ _ _ |>.symm
  have h_zero : h 0 = v 0 := by simp [h, v, b, state, fractionData]
  have h_step (p : ℕ) : h (p + 1) = h p * v (p + 1) := by
    simp [h, v, prod_range_succ, neg_mul]
  have q_zero : Q 0 = 1 := rfl
  have q_one : Q 1 = D 0 := rfl
  have n_zero : N 0 = 0 := rfl
  have n_one : N 1 = C (v 0) * X ^ k 0 := rfl
  have q_step (p : ℕ) : Q (p + 2) = D (p + 1) * Q (p + 1) - numerator p * Q p := rfl
  have n_step (p : ℕ) : N (p + 2) = D (p + 1) * N (p + 1) - numerator p * N p := rfl
  let I := invOfUnit (1 - X : PowerSeries ℤ) 1
  let S : PowerSeries ℤ := ∑ i ∈ range n, X ^ i
  have hI : (1 - X : PowerSeries ℤ) * I = 1 := by simp [I]
  have hS : S * (1 - X) = 1 - X ^ n := geom_sum_mul_neg X n
  have hs : S = (1 - X ^ n) * I := by
    calc
      S = S * ((1 - X) * I) := by rw [hI, mul_one]
      _ = (S * (1 - X)) * I := by ring
      _ = (1 - X ^ n) * I := by rw [hS]
  obtain ⟨F, equation, degrees, error⟩ : ∃ F : ℕ → PowerSeries ℤ,
      X ^ (n + 2) * F 0 ^ 2 + (X * S + (1 + X ^ n) * (1 - X)) * F 0 =
        X ^ (n - 1) ∧
      (∀ p, constantCoeff (Q p) = 1 ∧
        (∀ r, s p < r → coeff r (Q p) = 0) ∧
        (∀ r, s p ≤ r → coeff r (N p) = 0)) ∧
      ∀ p, ∃ R : PowerSeries ℤ,
        Q p * F 0 - N p = X ^ (2 * s p + k p) * R ∧ constantCoeff R = h p := by
    by_cases hn1 : n = 1
    · obtain ⟨F, he, hb, hr⟩ := golden_approximation k s v h D Q N
        (by intro p; simp [k, v, b, D, hn1]) s_zero s_step h_zero h_step
        q_zero q_one n_zero n_one q_step n_step
      refine ⟨F, ?_, hb, hr⟩
      have hS1 : S = 1 := by simp [S, hn1]
      rw [hn1, hS1]
      norm_num
      convert he using 1 <;> ring
    · obtain ⟨F, he, hb, hr⟩ := metallic_approximation a ha state state_zero
        state_step k s v h D Q N
        (by intro p; simp [k, v, b, D, hn1]) s_zero s_step h_zero h_step
        q_zero q_one n_zero n_one q_step n_step
      refine ⟨F, ?_, hb, hr⟩
      rw [an hn1] at he
      rw [hs]
      simpa only [quadraticData, I, mul_assoc] using he
  let Φ := S + X ^ (n + 1) * F 0
  have hn0 : n ≠ 0 := by omega
  have sconstant : constantCoeff S = 1 := by simp [hs, I, hn0]
  have hb : linearCoeff n = (1 + X ^ n) * (1 - X) - X * S := rfl
  have hsquare : X * S ^ 2 + linearCoeff n * S - 1 = -X ^ (2 * n) := by
    rw [hb]
    calc
      X * S ^ 2 + ((1 + X ^ n) * (1 - X) - X * S) * S - 1 =
          (1 + X ^ n) * (S * (1 - X)) - 1 := by ring
      _ = -X ^ (2 * n) := by rw [hS, two_mul, pow_add]; ring
  have metallic : IsMetallic n Φ := by
    refine ⟨by simp [Φ, sconstant], ?_⟩
    have he : X ^ (n + 2) * F 0 ^ 2 +
        (X * S + (1 + X ^ n) * (1 - X)) * F 0 - X ^ (n - 1) = 0 := by
      exact sub_eq_zero.mpr equation
    have hp : n + 1 + (n - 1) = 2 * n := by omega
    have htail : X * Φ ^ 2 + linearCoeff n * Φ - 1 =
        X ^ (n + 1) *
          (X ^ (n + 2) * F 0 ^ 2 + (X * S + (1 + X ^ n) * (1 - X)) * F 0 -
            X ^ (n - 1)) := by
      dsimp [Φ]
      rw [hb] at hsquare ⊢
      rw [← sub_eq_zero] at hsquare
      rw [pow_add, show n + 2 = (n + 1) + 1 by omega, pow_add, pow_one]
      have hpn : (X : PowerSeries ℤ) ^ (n + 1) * X ^ (n - 1) = X ^ (2 * n) := by
        rw [← pow_add, hp]
      linear_combination hsquare + hpn
    exact sub_eq_zero.mp (by rw [htail, he, mul_zero])
  have shifted (r : ℕ) : coeff (n + 1 + r) Φ = coeff r (F 0) := by
    dsimp [Φ]
    rw [map_add, coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel_left]
    have hz : coeff (n + 1 + r) S = 0 := by
      dsimp [S]
      rw [map_sum]
      apply sum_eq_zero
      intro i hi
      rw [coeff_X_pow, if_neg]
      simp only [mem_range] at hi
      omega
    rw [hz, zero_add]
  have unique (Ψ : PowerSeries ℤ) (hΨ : IsMetallic n Ψ) : Ψ = Φ := by
    have hu : IsUnit (linearCoeff n + X * (Ψ + Φ)) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      simp [linearCoeff, hn0]
    apply hu.mul_left_injective
    linear_combination hΨ.2 - metallic.2
  have k_period (p : ℕ) : k (p + L) = k p := by
    by_cases hn1 : n = 1
    · simp [k, L, hn1]
    · simp [k, L, hn1, state_period]
  have b_period (p : ℕ) : b (p + L) = b p := by
    by_cases hn1 : n = 1
    · simp [b, L, hn1]
    · simp [b, L, hn1, state_period]
  have sum_rotate (f : ℕ → ℕ) (hf : ∀ p, f (p + L) = f p) (p : ℕ) :
      (∑ i ∈ range L, f (p + i)) = ∑ i ∈ range L, f i := by
    obtain ⟨m, hm⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
    induction p with
    | zero => simp
    | succ p ih =>
      have hlast : f (p + 1 + m) = f p := by
        rw [show p + 1 + m = p + L by omega, hf]
      calc
        _ = (∑ i ∈ range m, f (p + 1 + i)) + f p := by
          rw [hm, sum_range_succ, hlast]
        _ = (∑ i ∈ range m, f (p + (i + 1))) + f p := by
          congr 1
          apply sum_congr rfl
          intro i hi
          congr 1
          omega
        _ = ∑ i ∈ range L, f (p + i) := by
          rw [hm, sum_range_succ']
          simp
        _ = _ := ih
  have prod_rotate (f : ℕ → ℤ) (hf : ∀ p, f (p + L) = f p) (p : ℕ) :
      (∏ i ∈ range L, f (p + i)) = ∏ i ∈ range L, f i := by
    obtain ⟨m, hm⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
    induction p with
    | zero => simp
    | succ p ih =>
      have hlast : f (p + 1 + m) = f p := by
        rw [show p + 1 + m = p + L by omega, hf]
      calc
        _ = (∏ i ∈ range m, f (p + 1 + i)) * f p := by
          rw [hm, prod_range_succ, hlast]
        _ = (∏ i ∈ range m, f (p + (i + 1))) * f p := by
          congr 1
          apply prod_congr rfl
          intro i hi
          congr 1
          omega
        _ = ∏ i ∈ range L, f (p + i) := by
          rw [hm, prod_range_succ']
          simp
        _ = _ := ih
  have weight0 : (∑ i ∈ range L, (k i + 1)) = P := by
    by_cases hn1 : n = 1
    · norm_num [L, P, k, hn1, sum_range_succ]
    · have hlist : List.ofFn (fun i : Fin L₀ => (fractionData a (state i)).1 + 1) =
          (cycle a).map (fun z => (fractionData a z).1 + 1) := by
        rw [← List.ofFn_getElem (xs := cycle a), List.map_ofFn]
        congr 1
        funext i
        rw [state_at i i.isLt]
        rfl
      simp only [L, k, P, if_neg hn1]
      rw [← Fin.sum_univ_eq_sum_range, ← List.sum_ofFn, hlist, weight, an hn1]
  have bprod0 : (∏ i ∈ range L, b i) = 1 := by
    by_cases hn1 : n = 1
    · norm_num [L, b, hn1, prod_range_succ]
    · have hlist : List.ofFn (fun i : Fin L₀ => (fractionData a (state i)).2.1) =
          (cycle a).map (fun z => (fractionData a z).2.1) := by
        rw [← List.ofFn_getElem (xs := cycle a), List.map_ofFn]
        congr 1
        funext i
        rw [state_at i i.isLt]
        rfl
      simp only [L, b, if_neg hn1]
      rw [← Fin.prod_univ_eq_prod_range, ← List.prod_ofFn, hlist]
      exact (cycle_sign a ha).1
  have s_period (p : ℕ) : s (p + L) = s p + P := by
    simp only [s, sum_range_add]
    rw [sum_rotate (fun i => k i + 1) (by intro i; rw [k_period]), weight0]
  have h_period (p : ℕ) : h (p + L) = h p := by
    dsimp [h]
    rw [show p + L + 1 = (p + 1) + L by omega, prod_range_add,
      prod_rotate b b_period, bprod0, mul_one]
  have bsquare (p : ℕ) : b p ^ 2 = 1 := by
    by_cases hn1 : n = 1
    · simp [b, hn1]
    · simp only [b, if_neg hn1]
      cases state p <;> norm_num [fractionData]
  have h_square (p : ℕ) : h p ^ 2 = 1 := by
    induction p with
    | zero =>
      simpa [h] using bsquare 0
    | succ p ih =>
      dsimp [h] at ih ⊢
      rw [prod_range_succ, ← neg_mul, mul_pow, ih, bsquare (p + 1), one_mul]
  have hsign (p : ℕ) : h p ∈ ({-1, 1} : Finset ℤ) := by
    have hh : (h p + 1) * (h p - 1) = 0 := by nlinarith [h_square p]
    simp only [mem_insert, mem_singleton]
    rcases mul_eq_zero.mp hh with he | he
    · left; omega
    · right; omega
  let c (p r : ℕ) : ℤ := coeff (s p - r) (Q p)
  have moments (p : ℕ) : c p (s p) = 1 ∧
      (∀ t, t < s p + k p →
        ∑ r ∈ range (s p + 1), c p r * coeff (n + 1 + r + t) Φ = 0) ∧
      (∑ r ∈ range (s p + 1),
        c p r * coeff (n + 1 + r + (s p + k p)) Φ) = h p := by
    obtain ⟨R, he, hr⟩ := error p
    have convolution (t : ℕ) :
        (∑ r ∈ range (s p + 1), c p r * coeff (n + 1 + r + t) Φ) =
          coeff (s p + t) (Q p * F 0) := by
      simp only [show ∀ r, n + 1 + r + t = n + 1 + (r + t) by intro r; omega,
        shifted, c]
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      have truncate :
          (∑ i ∈ range (s p + t + 1), coeff i (Q p) * coeff (s p + t - i) (F 0)) =
            ∑ i ∈ range (s p + 1), coeff i (Q p) * coeff (s p + t - i) (F 0) := by
        symm
        apply Finset.sum_subset (range_mono (by omega))
        intro i hi hnot
        have hi' : s p < i := by simp only [mem_range] at hnot; omega
        simp [(degrees p).2.1 i hi']
      rw [truncate, ← sum_range_reflect
        (fun i => coeff i (Q p) * coeff (s p + t - i) (F 0)) (s p + 1)]
      apply sum_congr rfl
      intro r hr
      have hr' : r ≤ s p := by simp only [mem_range] at hr; omega
      rw [show s p + 1 - 1 - r = s p - r by omega,
        show s p + t - (s p - r) = r + t by omega]
    refine ⟨by simpa [c] using (degrees p).1, ?_, ?_⟩
    · intro t ht
      rw [convolution]
      have ht' := congrArg (coeff (s p + t)) he
      rw [map_sub, (degrees p).2.2 _ (by omega), sub_zero, coeff_X_pow_mul',
        if_neg (by omega)] at ht'
      exact ht'
    · rw [convolution]
      have ht' := congrArg (coeff (s p + (s p + k p))) he
      rw [map_sub, (degrees p).2.2 _ (by omega), sub_zero, coeff_X_pow_mul',
        if_pos (by omega), show s p + (s p + k p) - (2 * s p + k p) = 0 by omega,
        coeff_zero_eq_constantCoeff, hr] at ht'
      exact ht'
  have spos (p : ℕ) : p ≤ s p := by
    induction p with
    | zero => omega
    | succ p ih => rw [s_step]; omega
  have normal (p : ℕ) := zero_run Φ (n + 1) (s p) (k p + 1) (c p) (h p)
    (by omega) (moments p).1
    (fun t ht => (moments p).2.1 t (by omega))
    (by simpa only [show s p + (k p + 1) - 1 = s p + k p by omega]
      using (moments p).2.2)
  have hunit (p : ℕ) : IsUnit (h p) := by
    apply Int.isUnit_iff.mpr
    have he := hsign p
    simp only [mem_insert, mem_singleton] at he
    exact he.symm
  have aunit : ∀ p, IsUnit (shiftedHankel Φ (n + 1) (s p)) := by
    intro p
    induction p with
    | zero =>
      rw [s_zero]
      change IsUnit (Matrix.of fun i j : Fin 0 => coeff (n + 1 + i.val + j.val) Φ).det
      rw [Matrix.det_fin_zero]
      exact isUnit_one
    | succ p ih =>
      rw [s_step, Nat.add_assoc, (normal p).1]
      exact ((isUnit_one.neg).pow _ |>.mul ((hunit p).pow _)).mul ih
  let w (p : ℕ) : ℤ := (-1) ^ (k p * (k p + 1) / 2) * h p ^ (k p + 1)
  have wperiod (p : ℕ) : w (p + L) = w p := by simp [w, k_period, h_period]
  have wprod : (∏ i ∈ range L, w i) = (-1 : ℤ) ^ n := by
    by_cases hn1 : n = 1
    · norm_num [w, L, k, h, b, hn1, prod_range_succ]
    · have index (i : ℕ) (hi : i < L) : state i = (cycle a).getD i .v₂ := by
        have hi' : i < L₀ := by simpa [L, hn1] using hi
        rw [List.getD_eq_getElem (cycle a) .v₂ hi']
        exact state_at i hi'
      have compare (i : ℕ) (hi : i < L) : w i =
          let z := (cycle a).getD i .v₂
          let ki := (fractionData a z).1
          let hp := -(∏ j ∈ range (i + 1),
            (fractionData a ((cycle a).getD j .v₂)).2.1)
          (-1 : ℤ) ^ (ki * (ki + 1) / 2) * hp ^ (ki + 1) := by
        have kh : k i = (fractionData a ((cycle a).getD i .v₂)).1 := by
          simp only [k, if_neg hn1]
          rw [index i hi]
        have hh : h i = -(∏ j ∈ range (i + 1),
            (fractionData a ((cycle a).getD j .v₂)).2.1) := by
          dsimp [h]
          congr 1
          apply prod_congr rfl
          intro j hj
          simp only [b, if_neg hn1]
          rw [index j (by simp only [mem_range] at hj; omega)]
        simp only [w, kh, hh]
      calc
        _ = _ := prod_congr rfl (fun i hi => compare i (mem_range.mp hi))
        _ = _ := by simpa only [L, L₀, if_neg hn1, an hn1] using (cycle_sign a ha).2
  have determinant_product (p q : ℕ) : shiftedHankel Φ (n + 1) (s (p + q)) =
      (∏ i ∈ range q, w (p + i)) * shiftedHankel Φ (n + 1) (s p) := by
    induction q with
    | zero => simp
    | succ q ih =>
      have he : shiftedHankel Φ (n + 1) (s (p + q + 1)) =
          w (p + q) * shiftedHankel Φ (n + 1) (s (p + q)) := by
        rw [s_step]
        simpa only [w, Nat.add_assoc, Nat.add_sub_cancel, Nat.mul_comm]
          using (normal (p + q)).1
      rw [show p + (q + 1) = p + q + 1 by omega, he, ih, prod_range_succ]
      ring
  have determinant_period (p : ℕ) : shiftedHankel Φ (n + 1) (s (p + L)) =
      (-1 : ℤ) ^ n * shiftedHankel Φ (n + 1) (s p) := by
    rw [determinant_product, prod_rotate w wperiod, wprod]
  have determinant_multiple (q : ℕ) : shiftedHankel Φ (n + 1) (s (q * L)) =
      (-1 : ℤ) ^ (n * q) := by
    induction q with
    | zero =>
      rw [Nat.zero_mul, s_zero, Nat.mul_zero, pow_zero]
      exact Matrix.det_fin_zero
    | succ q ih =>
      rw [Nat.succ_mul, determinant_period, ih, Nat.mul_succ, pow_add]
      ring
  have bmultiple (q : ℕ) : (∏ i ∈ range (q * L), b i) = 1 := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul, prod_range_add, prod_rotate b b_period, bprod0, ih, mul_one]
  have unit_abs (z : ℤ) (hu : IsUnit z) : z.natAbs = 1 := by
    rcases Int.isUnit_iff.mp hu with rfl | rfl <;> norm_num
  have base_bound (j : ℕ) : (shiftedHankel Φ (n + 1) j).natAbs ≤ 1 := by
    obtain ⟨p, hj, hnext⟩ : ∃ p, s p ≤ j ∧ j < s (p + 1) := by
      induction j with
      | zero => exact ⟨0, by rw [s_zero], by rw [s_step, s_zero]; omega⟩
      | succ j ih =>
        obtain ⟨p, hj, hnext⟩ := ih
        by_cases hlt : j + 1 < s (p + 1)
        · exact ⟨p, by omega, hlt⟩
        · refine ⟨p + 1, by omega, ?_⟩
          rw [s_step]
          omega
    by_cases he : j = s p
    · subst j
      exact le_of_eq (unit_abs _ (aunit p))
    · rw [(normal p).2.1 j (by omega) (by rw [s_step] at hnext; omega)]
      simp
  let t (p : ℕ) := coeff (s p) (Q p)
  let u (p : ℕ) := if s p = 0 then 0 else coeff (s p - 1) (Q p)
  let d (p : ℕ) := coeff (k p + 1) (D p)
  let e (p : ℕ) := coeff (k p) (D p)
  have dsupport (p r : ℕ) (hr : k p + 1 < r) : coeff r (D p) = 0 := by
    by_cases hn1 : n = 1
    · simp only [D, k, if_pos hn1] at hr ⊢
      split_ifs with hp
      · simp only [hp, if_true] at hr
        simp [coeff_X, coeff_X_pow, show r ≠ 0 by omega,
          show r ≠ 1 by omega, show r ≠ 2 by omega]
      · simp only [hp, if_false] at hr
        simp [coeff_X, show r ≠ 0 by omega, show r ≠ 1 by omega]
    · simp only [D, k, if_neg hn1] at hr ⊢
      exact (denominator _ (valid p)).2 r hr
  have top (U V : PowerSeries ℤ) (a b : ℕ)
      (hU : ∀ i, a < i → coeff i U = 0)
      (hV : ∀ i, b < i → coeff i V = 0) :
      coeff (a + b) (U * V) = coeff a U * coeff b V := by
    rw [coeff_mul]
    apply sum_eq_single (a, b)
    · intro x hx hne
      have he := mem_antidiagonal.mp hx
      by_cases hd : a < x.1
      · simp [hU x.1 hd]
      · have hfst : x.1 ≠ a := by
          intro eq
          apply hne
          exact Prod.ext eq (by omega)
        simp [hV x.2 (by omega)]
    · simp
  have top2 (U V : PowerSeries ℤ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
      (hU : ∀ i, a < i → coeff i U = 0)
      (hV : ∀ i, b < i → coeff i V = 0) :
      coeff (a + b - 1) (U * V) =
        coeff a U * coeff (b - 1) V + coeff (a - 1) U * coeff b V := by
    rw [coeff_mul]
    have h₁ : (a, b - 1) ∈ antidiagonal (a + b - 1) := by
      rw [mem_antidiagonal]; omega
    have h₂ : (a - 1, b) ∈ antidiagonal (a + b - 1) := by
      rw [mem_antidiagonal]; omega
    have hne : (a, b - 1) ≠ (a - 1, b) := by intro he; have hh := congrArg Prod.fst he; omega
    have terms (z : ℕ × ℕ) (hz : z ∈ antidiagonal (a + b - 1)) :
        coeff z.1 U * coeff z.2 V =
          (if z = (a, b - 1) then coeff a U * coeff (b - 1) V else 0) +
          (if z = (a - 1, b) then coeff (a - 1) U * coeff b V else 0) := by
      by_cases h₃ : z = (a, b - 1)
      · subst z; simp [hne]
      by_cases h₄ : z = (a - 1, b)
      · subst z; simp [hne.symm]
      simp only [h₃, h₄, if_false, zero_add]
      have he := mem_antidiagonal.mp hz
      by_cases ht : a < z.1
      · simp [hU _ ht]
      · have hv : b < z.2 := by
          by_contra h
          have cases : z.1 = a ∨ z.1 = a - 1 := by omega
          rcases cases with hh | hh
          · exact h₃ (Prod.ext hh (by omega))
          · exact h₄ (Prod.ext hh (by omega))
        simp [hV _ hv]
    rw [sum_congr rfl terms, sum_add_distrib]
    simp [h₁, h₂]
  have t0 : t 0 = 1 := by simp [t, q_zero, s_zero]
  have u0 : u 0 = 0 := by simp [u, s_zero]
  have t1 : t 1 = d 0 := by simp [t, d, q_one, s_step, s_zero]
  have u1 : u 1 = e 0 := by simp [u, e, q_one, s_step, s_zero]
  have jetrec (p : ℕ) :
      t (p + 2) = d (p + 1) * t (p + 1) - v (p + 1) * t p ∧
      u (p + 2) = d (p + 1) * u (p + 1) + e (p + 1) * t (p + 1) -
        v (p + 1) * u p := by
    have hs1 := s_step p
    have hs2 : s (p + 2) = s (p + 1) + k (p + 1) + 1 := by
      simpa only [Nat.add_assoc] using s_step (p + 1)
    have he : s (p + 2) = k p + k (p + 1) + 2 + s p := by omega
    have hp1 : s (p + 1) ≠ 0 := by have hh := spos (p + 1); omega
    have hp2 : s (p + 2) ≠ 0 := by have hh := spos (p + 2); omega
    have hi : s (p + 2) = (k (p + 1) + 1) + s (p + 1) := by omega
    have htop := top (D (p + 1)) (Q (p + 1)) (k (p + 1) + 1) (s (p + 1))
      (dsupport (p + 1)) (degrees (p + 1)).2.1
    have hsecond := top2 (D (p + 1)) (Q (p + 1)) (k (p + 1) + 1) (s (p + 1))
      (by omega) (by omega) (dsupport (p + 1)) (degrees (p + 1)).2.1
    constructor
    · dsimp only [t]
      rw [q_step, map_sub, hi, htop]
      dsimp only [numerator]
      rw [mul_assoc, coeff_C_mul, ← hi, he, coeff_X_pow_mul', if_pos (by omega),
        Nat.add_sub_cancel_left]
    · have hlow : coeff (s (p + 2) - 1) (numerator p * Q p) = v (p + 1) * u p := by
        dsimp only [numerator]
        rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
        by_cases hp : s p = 0
        · rw [if_neg (by omega)]
          simp [u, hp]
        · rw [if_pos (by omega), show s (p + 2) - 1 -
            (k p + k (p + 1) + 2) = s p - 1 by omega]
          simp [u, hp]
      dsimp only [u]
      rw [if_neg hp2, q_step, map_sub, hi, hsecond, ← hi, hlow]
      simp only [u, if_neg hp1, Nat.add_sub_cancel, d, e, t]
  have wordlen : (jetWord n).length = L := by
    by_cases hn1 : n = 1
    · simp [jetWord, L, hn1]
    · simp only [jetWord, if_neg hn1, List.length_map, L]
      dsimp [L₀]
      rw [an hn1]
  have lookup (p : ℕ) : (jetWord n)[p % (jetWord n).length]! =
      (inl (d p) + inr (e p), b p) := by
    rw [wordlen]
    by_cases hn1 : n = 1
    · have hr := Nat.mod_lt p (by omega : 0 < 3)
      obtain he | he | he : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
      all_goals norm_num [jetWord, hn1, L, d, e, k, b, D, he, coeff_X, coeff_X_pow]
    · simp only [jetWord, if_neg hn1]
      rw [← an hn1]
      have hi : p % L₀ < (cycle a).length := Nat.mod_lt p L₀pos
      simp only [L, if_neg hn1]
      rw [getElem!_pos _ _ (by simpa using hi), List.getElem_map,
        ← state_at _ hi, ← state_mod]
      simp [d, e, k, b, D, hn1]
  let jet (p : ℕ) : DualNumber ℤ := inl (t p) + inr (u p)
  let pair (p : ℕ) := (jet p, if p = 0 then 0 else jet (p - 1))
  have pair0 : pair 0 = (1, 0) := by simp [pair, jet, t0, u0]
  have pair_step (p : ℕ) : pair (p + 1) =
      jetStep (pair p) ((jetWord n)[p % (jetWord n).length]!) := by
    rw [lookup]
    cases p with
    | zero => simp [pair, jet, jetStep, t1, u1, t0, u0]
    | succ p =>
      have ht := (jetrec p).1
      have hu := (jetrec p).2
      simp only [v, show p + 1 ≠ 0 by omega, if_false] at ht hu
      apply Prod.ext
      · apply TrivSqZeroExt.ext <;>
          simp [pair, jet, jetStep, ht, hu, Nat.add_assoc,
            -DualNumber.inr_eq_smul_eps] <;> ring
      · simp [pair, jetStep, Nat.add_assoc]
  let lam : ℕ := if n = 1 then 1 else 2 * n + 1
  have lampos : 1 ≤ lam := by dsimp [lam]; split_ifs <;> omega
  have Lthree : 3 ≤ L := by
    dsimp [L]
    split_ifs
    · omega
    · dsimp [L₀]
      rw [length_eq]
      omega
  have smultiple (q : ℕ) : s (q * L) = q * P := by
    induction q with
    | zero => simpa using s_zero
    | succ q ih => rw [Nat.succ_mul, s_period, ih, Nat.succ_mul]
  have subsequence (q : ℕ) (hq : 0 < q) :
      (shiftedHankel Φ (n + 3) (q * P - 1)).natAbs = 2 * q * lam := by
    let r := q * L
    let p := r - 1
    have hr : 3 ≤ r := by dsimp [r]; nlinarith
    have hs : 1 ≤ s p := by have he := spos p; have hp : p = r - 1 := rfl; omega
    have hsucc : p + 1 = r := by dsimp [p]; omega
    have hsnext : s r = s p + k p + 1 := by rw [← hsucc, s_step]
    have hjet := cycle_transfer n hn pair pair0 pair_step q
    rw [wordlen] at hjet
    have ht : t r = 1 := by
      simpa [r, pair, jet, -DualNumber.inr_eq_smul_eps] using
        congrArg (fun z => TrivSqZeroExt.fst z.1) hjet
    have hb0 : t p = 0 := by
      simpa [r, p, pair, jet, show q * L ≠ 0 by omega,
        -DualNumber.inr_eq_smul_eps] using
        congrArg (fun z => TrivSqZeroExt.fst z.2) hjet
    have hb1 : u p = 2 * (q : ℤ) * (lam : ℤ) := by
      have hlam : (lam : ℤ) = if n = 1 then 1 else 2 * (n : ℤ) + 1 := by
        dsimp [lam]
        split_ifs <;> simp
      simpa [r, p, pair, jet, show q * L ≠ 0 by omega, hlam,
        -DualNumber.inr_eq_smul_eps] using
        congrArg (fun z => TrivSqZeroExt.snd z.2) hjet
    let prev (j : ℕ) : ℤ := if j ≤ s p then c p j else 0
    have truncate (z : ℕ) : (∑ j ∈ range (s r),
        prev j * coeff (n + 1 + j + z) Φ) =
        ∑ j ∈ range (s p + 1), c p j * coeff (n + 1 + j + z) Φ := by
      have hf : (range (s r)).filter (fun j => j ≤ s p) = range (s p + 1) := by
        ext j
        simp only [mem_filter, mem_range]
        omega
      simp only [prev, ite_mul, zero_mul]
      rw [← sum_filter, hf]
    have hc0 : c r 0 = 1 := by simpa [c, t] using ht
    have hp0 : prev 0 = 0 := by simpa [prev, c, t] using hb0
    have hp1 : prev 1 = 2 * (q : ℤ) * (lam : ℤ) := by
      simpa [prev, c, u, hs, show s p ≠ 0 by omega] using hb1
    have co := normal_cofactor Φ (n + 1) (s r) (by have he := spos r; omega)
      (c r) prev (h p) (moments r).1 (by intro he; have hz := spos r; omega)
      (fun z hz => (moments r).2.1 z (by omega))
      (by intro z hz; rw [truncate]; apply (moments p).2.1; omega)
      (by rw [truncate]; simpa [hsnext] using (moments p).2.2) (aunit r)
    rw [hc0, hp0, hp1, mul_zero, one_mul, zero_sub] at co
    have hpminus : h p = -1 := by
      dsimp [h]
      rw [hsucc]
      dsimp [r]
      rw [bmultiple]
    have hm : s r = q * P := smultiple q
    have signed : shiftedHankel Φ (n + 3) (q * P - 1) =
        (-1 : ℤ) ^ (n * q) * (2 * (q : ℤ) * (lam : ℤ)) := by
      rw [hpminus, show shiftedHankel Φ (n + 1) (s r) = (-1 : ℤ) ^ (n * q)
        from determinant_multiple q, hm, show n + 1 + 2 = n + 3 by omega] at co
      linear_combination -co
    rw [signed, Int.natAbs_mul, Int.natAbs_pow]
    norm_num [Int.natAbs_mul, Int.natAbs_natCast]
  have first_unbounded (M : ℕ) :
      ∃ j, M < (shiftedHankel Φ (n + 3) j).natAbs := by
    refine ⟨(M + 1) * P - 1, ?_⟩
    rw [subsequence (M + 1) (by omega)]
    nlinarith
  refine ⟨?_, ?_⟩
  · by_cases hn1 : n = 1
    · exact ⟨Φ, metallic⟩
    · exact (MetallicHankel.result n (by omega)).1
  · intro Ψ hΨ ℓ hℓ M
    rw [unique Ψ hΨ]
    by_cases he : ℓ = n + 3
    · subst ℓ
      exact first_unbounded M
    · by_contra hf
      have upper (j : ℕ) : (shiftedHankel Φ ℓ j).natAbs ≤ M := by
        exact Nat.le_of_not_gt (fun hj => hf ⟨j, hj⟩)
      let M' := max M 1
      have hb := MetallicHankelUnboundedStrip.bounded_strip Φ (n + 1) ℓ
        (4 * (n + 5)) M' (by omega) (by dsimp [M']; omega)
        (coefficient_growth n hn Φ metallic)
        (fun j => (base_bound j).trans (by dsimp [M']; omega))
        (fun j => (upper j).trans (le_max_left _ _))
      obtain ⟨j, hj⟩ := first_unbounded
        (2 ^ (Nat.log2 M' + 2 * ((n + 3) - (n + 1)) * (ℓ - (n + 3)) + 1))
      have ht := hb (n + 3) j (by omega) hℓ
      omega

end D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnbounded
