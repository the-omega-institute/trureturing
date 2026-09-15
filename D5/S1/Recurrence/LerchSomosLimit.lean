/- GID: D5/S1/Recurrence/LerchSomosLimit
   generality: I
   mirror-B: D5/B/S1/Recurrence/LerchSomosLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Meijer's Lerch convolution sequence converges to the Somos constant. -/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

/-!
The LP-limit conjecture in Meijer's June 27, 2016 comment on OEIS A112302.
The Lerch normalization is Phi(1/2,s,1) = 2 Li_s(1/2).
The intermediate constant series is Coffey (2015), Proposition 5(b), Eq. (1.25).
All auxiliary constructions and proofs are local to result.
-/
namespace D5.S1.Recurrence.LerchSomosLimit

noncomputable def LerchKernel (s : ℕ) : ℝ :=
  ∑' j : ℕ, (1 / 2 : ℝ)^j / ((j : ℝ) + 1)^s

noncomputable def SomosConstant : ℝ :=
  Real.exp (∑' j : ℕ, Real.log ((j : ℝ) + 1) / (2 : ℝ)^(j + 1))

def LPSource (a : ℕ → ℝ) : Prop :=
  a 0 = 1 ∧ ∀ n : ℕ, 0 < n →
    a n = (1 / (n : ℝ)) *
      ∑ k : Fin n, LerchKernel (n - k.val) * a k.val

theorem result :
  (∀ s : ℕ, 0 < s →
    Summable (fun j : ℕ => (1 / 2 : ℝ)^j / ((j : ℝ) + 1)^s)) ∧
  Summable (fun j : ℕ => Real.log ((j : ℝ) + 1) / (2 : ℝ)^(j + 1)) ∧
  (∃! a : ℕ → ℝ, LPSource a) ∧
  (∀ a : ℕ → ℝ, LPSource a →
    Filter.Tendsto a Filter.atTop (nhds SomosConstant))
 := by
  classical
  have hgeom : Summable (fun j : ℕ => (1 / 2 : ℝ)^j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hkernel : ∀ s : ℕ, 0 < s →
      Summable (fun j : ℕ => (1 / 2 : ℝ)^j / ((j : ℝ) + 1)^s) := by
    intro s hs
    refine hgeom.of_nonneg_of_le (fun j => by positivity) ?_
    intro j
    exact div_le_self (by positivity) (one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) j; linarith))
  have hlog : Summable (fun j : ℕ =>
      Real.log ((j : ℝ) + 1) / (2 : ℝ)^(j + 1)) := by
    have hm : Summable (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ)^j) := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one
        (R := ℝ) 1 (r := 1 / 2) (by norm_num)
    refine (hm.mul_right (1 / 2)).of_nonneg_of_le (fun j => by
      exact div_nonneg (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) j; linarith)) (by positivity)) ?_
    intro j
    calc
      Real.log ((j : ℝ) + 1) / (2 : ℝ)^(j + 1) ≤
          (j : ℝ) / (2 : ℝ)^(j + 1) := by
        gcongr
        simpa using Real.log_le_sub_one_of_pos (show 0 < (j : ℝ) + 1 by positivity)
      _ = (j : ℝ) * (1 / 2 : ℝ)^j * (1 / 2) := by
        rw [div_pow, one_pow, pow_succ]
        ring
  let a : ℕ → ℝ := Nat.strongRec fun n ih =>
    if hn : n = 0 then 1 else (1 / (n : ℝ)) *
      ∑ k : Fin n, LerchKernel (n - k.val) * ih k.val k.isLt
  have haeq (n : ℕ) : a n = if hn : n = 0 then 1 else
      (1 / (n : ℝ)) * ∑ k : Fin n, LerchKernel (n - k.val) * a k.val := by
    dsimp only [a]
    rw [Nat.strongRec_eq]
  have ha : LPSource a := by
    constructor
    · simpa using haeq 0
    · intro n hn
      simpa [Nat.ne_of_gt hn] using haeq n
  have hu : ∀ b : ℕ → ℝ, LPSource b → b = a := by
    intro b hb
    funext n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n = 0
      · subst n
        exact hb.1.trans ha.1.symm
      · rw [hb.2 n (Nat.pos_of_ne_zero hn), ha.2 n (Nat.pos_of_ne_zero hn)]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        rw [ih k.val k.isLt]
  clear_value a
  let q : ℝ := 1 / 2
  let r : ℕ → ℝ := fun n => LerchKernel n - 1
  have hrt (n : ℕ) (hn : 0 < n) : r n =
      ∑' j : ℕ, (1 / 2 : ℝ)^(j+1) / ((j : ℝ) + 2)^n := by
    have ht := (hkernel n hn).tsum_eq_zero_add
    dsimp [r, LerchKernel]
    simp only [pow_zero, Nat.cast_zero, zero_add, one_pow, div_one] at ht
    rw [ht]
    simp only [Nat.cast_add, Nat.cast_one]
    have hj (j : ℕ) : (j : ℝ) + 1 + 1 = (j : ℝ) + 2 := by ring
    simp only [hj]
    ring
  have hr (n : ℕ) (hn : 0 < n) : 0 ≤ r n ∧ r n ≤ q^n := by
    rw [hrt n hn]
    constructor
    · exact tsum_nonneg (fun j => by positivity)
    · have hmaj : Summable (fun j : ℕ => (1 / 2 : ℝ)^(j+1) / (2 : ℝ)^n) :=
        ((summable_nat_add_iff 1).mpr hgeom).div_const _
      have ht : Summable (fun j : ℕ => (1 / 2 : ℝ)^(j+1) / ((j : ℝ) + 2)^n) := by
        convert (summable_nat_add_iff 1).mpr (hkernel n hn) using 1
        congr 1
        funext j
        simp only [Nat.cast_add, Nat.cast_one]
        congr 2
        ring
      calc
        (∑' j : ℕ, (1 / 2 : ℝ)^(j+1) / ((j : ℝ) + 2)^n) ≤
            ∑' j : ℕ, (1 / 2 : ℝ)^(j+1) / (2 : ℝ)^n := by
          apply Summable.tsum_le_tsum _ ht hmaj
          intro j
          gcongr
          exact le_add_of_nonneg_left (Nat.cast_nonneg j)
        _ = q^n := by
          rw [tsum_div_const]
          have hg : (∑' j : ℕ, (1 / 2 : ℝ)^(j+1)) = 1 := by
            have hh := hgeom.tsum_eq_zero_add
            rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at hh
            norm_num at hh
            linarith
          rw [hg]
          dsimp [q]
          rw [div_pow, one_pow]
  let c : ℕ → ℝ := Nat.strongRec fun n ih =>
    if hn : n = 0 then 1 else (1 / (n : ℝ)) *
      ∑ k : Fin n, r (k.val + 1) * ih (n - 1 - k.val) (by omega)
  have hceq (n : ℕ) : c n = if hn : n = 0 then 1 else
      (1 / (n : ℝ)) * ∑ k : Fin n, r (k.val + 1) * c (n - 1 - k.val) := by
    dsimp only [c]
    rw [Nat.strongRec_eq]
  have hc0 : c 0 = 1 := by simpa using hceq 0
  have hcrec (n : ℕ) : (n : ℝ) * c n =
      ∑ k ∈ Finset.range n, r (k + 1) * c (n - 1 - k) := by
    by_cases hn : n = 0
    · subst n; simp
    · rw [hceq n, dif_neg hn, ← Fin.sum_univ_eq_sum_range]
      field_simp
  clear_value c
  have hcbound (n : ℕ) : 0 ≤ c n ∧ c n ≤ q^n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n = 0
      · subst n; simp [hc0]
      · rw [hceq n, dif_neg hn]
        have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        constructor
        · apply mul_nonneg (by positivity)
          apply Finset.sum_nonneg
          intro k hk
          exact mul_nonneg (hr (k.val+1) (by omega)).1 (ih _ (by omega)).1
        · calc
            (1 / (n : ℝ)) * ∑ k : Fin n, r (k.val+1) * c (n-1-k.val) ≤
                (1 / (n : ℝ)) * ∑ k : Fin n, q^(k.val+1) * q^(n-1-k.val) := by
              gcongr with k
              · exact (ih _ (by omega)).1
              · exact (hr (k.val+1) (by omega)).2
              · exact (ih _ (by omega)).2
            _ = q^n := by
              have hp (k : Fin n) : q^(k.val+1) * q^(n-1-k.val) = q^n := by
                rw [← pow_add]
                congr 1
                omega
              simp only [hp, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              field_simp
  have hcsum : Summable c := hgeom.of_nonneg_of_le (fun n => (hcbound n).1)
    (fun n => (hcbound n).2)
  let T : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n+1), c i
  have hT0 : T 0 = 1 := by simp [T, hc0]
  have hTstep (n : ℕ) : T (n+1) = T n + c (n+1) := by
    exact Finset.sum_range_succ _ _
  have hK (n : ℕ) : LerchKernel n = r n + 1 := by dsimp [r]; ring
  have hRT (n : ℕ) :
      (∑ k ∈ Finset.range n, LerchKernel (k+1) * T (n-1-k)) = (n : ℝ) * T n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hshift (k : ℕ) (hk : k ∈ Finset.range n) :
          T (n-k) = T (n-1-k) + c (n-k) := by
        have he : n-k = n-1-k+1 := by have := Finset.mem_range.mp hk; omega
        conv_lhs => rw [he, hTstep]
        rw [← he]
      have hsumc : (∑ k ∈ Finset.range (n+1), c (n-k)) = T n := by
        simpa [T] using Finset.sum_range_reflect c (n+1)
      have hsumr : (∑ k ∈ Finset.range (n+1), r (k+1) * c (n-k)) =
          (n+1 : ℝ) * c (n+1) := by
        simpa using (hcrec (n+1)).symm
      have hsumK : (∑ k ∈ Finset.range (n+1), LerchKernel (k+1) * c (n-k)) =
          (n+1 : ℝ) * c (n+1) + T n := by
        simp_rw [hK, add_mul, one_mul]
        rw [Finset.sum_add_distrib, hsumr, hsumc]
        ring
      calc
        (∑ k ∈ Finset.range (n+1), LerchKernel (k+1) * T (n+1-1-k)) =
            (∑ k ∈ Finset.range n, LerchKernel (k+1) * (T (n-1-k) + c (n-k))) +
              LerchKernel (n+1) := by
          rw [Finset.sum_range_succ]
          simp only [Nat.add_sub_cancel, Nat.sub_self, hT0, mul_one]
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          rw [hshift k hk]
        _ = (n : ℝ) * T n +
            ∑ k ∈ Finset.range (n+1), LerchKernel (k+1) * c (n-k) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, ih, Finset.sum_range_succ]
          simp [hc0, add_assoc]
        _ = (n+1 : ℝ) * T (n+1) := by
          rw [hsumK, hTstep]
          ring
        _ = ((n+1 : ℕ) : ℝ) * T (n+1) := by norm_cast
  have hTsource : LPSource T := by
    refine ⟨hT0, ?_⟩
    intro n hn
    rw [Fin.sum_univ_eq_sum_range (fun k => LerchKernel (n-k) * T k)]
    have href : (∑ k ∈ Finset.range n, LerchKernel (n-k) * T k) =
        ∑ k ∈ Finset.range n, LerchKernel (k+1) * T (n-1-k) := by
      rw [← Finset.sum_range_reflect (fun k => LerchKernel (n-k) * T k) n]
      apply Finset.sum_congr rfl
      intro k hk
      have he : n - (n-1-k) = k+1 := by have := Finset.mem_range.mp hk; omega
      rw [he]
    rw [href, hRT]
    have hnn : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp
  have hTa : T = a := hu T hTsource
  have ha_limit : Filter.Tendsto a Filter.atTop (nhds (∑' n, c n)) := by
    rw [← hTa]
    exact hcsum.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  clear_value T
  let H : ℝ → ℝ := fun x => ∑' n : ℕ, c n * x^n
  let G : ℝ → ℝ := fun x => ∑' n : ℕ, r (n+1) * x^(n+1) / (n+1 : ℝ)
  let B : ℝ → ℝ := fun x => ∑' n : ℕ, r (n+1) * x^n
  let U : Set ℝ := Set.Ioo (-(3/2)) (3/2)
  have hU0 : (0 : ℝ) ∈ U := by norm_num [U]
  have hU1 : (1 : ℝ) ∈ U := by norm_num [U]
  have hUabs {x : ℝ} (hx : x ∈ U) : |x| ≤ 3/2 :=
    (abs_lt.mpr hx).le
  have hgeom34 : Summable (fun n : ℕ => (3/4 : ℝ)^n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hgeom34n : Summable (fun n : ℕ => (n : ℝ)*(3/4 : ℝ)^n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one
      (R := ℝ) 1 (r := 3/4) (by norm_num)
  have hHbound (n : ℕ) {x : ℝ} (hx : x ∈ U) : ‖c n*x^n‖ ≤ (3/4 : ℝ)^n := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hcbound n).1, norm_pow, Real.norm_eq_abs]
    calc
      c n * |x|^n ≤ q^n * (3/2 : ℝ)^n := by gcongr; exact (hcbound n).2; exact hUabs hx
      _ = (3/4 : ℝ)^n := by rw [← mul_pow]; norm_num [q]
  have hHsum {x : ℝ} (hx : x ∈ U) : Summable (fun n : ℕ => c n*x^n) :=
    hgeom34.of_norm_bounded (fun n => hHbound n hx)
  have hBbound (n : ℕ) {x : ℝ} (hx : x ∈ U) : ‖r (n+1)*x^n‖ ≤ (3/4 : ℝ)^n := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hr (n+1) (by omega)).1,
      norm_pow, Real.norm_eq_abs]
    calc
      r (n+1) * |x|^n ≤ q^(n+1) * (3/2 : ℝ)^n := by
        gcongr
        · exact (hr (n+1) (by omega)).2
        · exact hUabs hx
      _ = (3/4 : ℝ)^n * (1/2) := by
        calc
          _ = (q*(3/2))^n * q := by rw [pow_succ, mul_pow]; ring
          _ = _ := by norm_num [q]
      _ ≤ (3/4 : ℝ)^n := mul_le_of_le_one_right (by positivity) (by norm_num)
  have hBsum {x : ℝ} (hx : x ∈ U) : Summable (fun n : ℕ => r (n+1)*x^n) :=
    hgeom34.of_norm_bounded (fun n => hBbound n hx)
  have hHdBound (n : ℕ) {x : ℝ} (hx : x ∈ U) :
      ‖c n * ((n : ℝ)*x^(n-1))‖ ≤ (n : ℝ)*(3/4 : ℝ)^n := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hcbound n).1,
      norm_mul, Real.norm_natCast, norm_pow, Real.norm_eq_abs]
    have hp : |x|^(n-1) ≤ (3/2 : ℝ)^n := calc
      |x|^(n-1) ≤ (3/2 : ℝ)^(n-1) := pow_le_pow_left₀ (abs_nonneg _) (hUabs hx) _
      _ ≤ (3/2 : ℝ)^n := pow_le_pow_right₀ (by norm_num) (by omega)
    calc
      c n * ((n : ℝ)*|x|^(n-1)) ≤ q^n * ((n : ℝ)*(3/2 : ℝ)^n) := by
        gcongr
        exact (hcbound n).2
      _ = (n : ℝ)*(3/4 : ℝ)^n := by
        calc
          _ = (n : ℝ)*(q*(3/2))^n := by rw [mul_pow]; ring
          _ = _ := by norm_num [q]
  have hHd {x : ℝ} (hx : x ∈ U) :
      HasDerivAt H (∑' n : ℕ, c n * ((n : ℝ)*x^(n-1))) x := by
    exact hasDerivAt_tsum_of_isPreconnected hgeom34n isOpen_Ioo isPreconnected_Ioo
      (fun n y hy => (hasDerivAt_pow n y).const_mul (c n))
      (fun n y hy => hHdBound n hy) hU0 (hHsum hU0) hx
  have hGd {x : ℝ} (hx : x ∈ U) : HasDerivAt G (B x) x := by
    apply hasDerivAt_tsum_of_isPreconnected hgeom34 isOpen_Ioo isPreconnected_Ioo
      (g' := fun n y => r (n+1)*y^n) _ (fun n y hy => hBbound n hy) hU0 _ hx
    · intro n y hy
      convert! ((hasDerivAt_pow (n+1) y).const_mul (r (n+1))).div_const (n+1 : ℝ) using 1
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      field_simp
    · simp only [zero_pow (Nat.succ_ne_zero _), mul_zero, zero_div]
      exact summable_zero
  have hODE {x : ℝ} (hx : x ∈ U) : HasDerivAt H (B x * H x) x := by
    have hsd : Summable (fun n : ℕ => c n * ((n : ℝ)*x^(n-1))) :=
      hgeom34n.of_norm_bounded (fun n => hHdBound n hx)
    have hBn : Summable (fun n : ℕ => ‖r (n+1)*x^n‖) :=
      hgeom34.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hBbound n hx)
    have hHn : Summable (fun n : ℕ => ‖c n*x^n‖) :=
      hgeom34.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hHbound n hx)
    convert hHd hx using 1
    dsimp only [B, H]
    rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hBn hHn,
      hsd.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.add_sub_cancel]
    apply tsum_congr
    intro n
    have hp (k : ℕ) (hk : k ∈ Finset.range (n+1)) :
        r (k+1)*x^k*(c (n-k)*x^(n-k)) = (r (k+1)*c (n-k))*x^n := by
      have he : k+(n-k)=n := Nat.add_sub_of_le (Finset.mem_range_succ_iff.mp hk)
      calc
        _ = (r (k+1)*c (n-k))*(x^k*x^(n-k)) := by ring
        _ = _ := by rw [← pow_add, he]
    rw [Finset.sum_congr rfl hp, ← Finset.sum_mul]
    have hc := hcrec (n+1)
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hc
    rw [← hc]
    push_cast
    ring
  have hFderiv {x : ℝ} (hx : x ∈ U) :
      HasDerivAt (fun x => H x * Real.exp (-G x)) 0 x := by
    have hh := (hODE hx).mul ((hGd hx).neg.exp)
    convert! hh using 1
    ring
  have hconstant : H 1 * Real.exp (-G 1) = H 0 * Real.exp (-G 0) := by
    apply IsOpen.is_const_of_deriv_eq_zero isOpen_Ioo isPreconnected_Ioo
      (fun x hx => (hFderiv hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hFderiv hx).deriv) hU1 hU0
  have hH0 : H 0 = 1 := by
    dsimp [H]
    rw [tsum_eq_single 0]
    · simp [hc0]
    · intro n hn
      simp [zero_pow hn]
  have hG0 : G 0 = 0 := by simp [G]
  have hH1 : (∑' n : ℕ, c n) = Real.exp (G 1) := by
    rw [hH0, hG0, neg_zero, Real.exp_zero, mul_one] at hconstant
    have hh := congrArg (fun v => v * Real.exp (G 1)) hconstant
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, one_mul] at hh
    simpa [H] using hh
  let F : ℕ → ℕ → ℝ := fun n j =>
    (1/2 : ℝ)^(j+1) / ((j : ℝ)+2)^(n+1) / (n+1 : ℝ)
  have hFnonneg (n j : ℕ) : 0 ≤ F n j := by dsimp [F]; positivity
  have hgeomshift : Summable (fun n : ℕ => (1/2 : ℝ)^(n+1)) :=
    (summable_nat_add_iff 1).mpr hgeom
  have hdouble : Summable (fun p : ℕ × ℕ => F p.1 p.2) := by
    have hm : Summable (fun p : ℕ × ℕ => (1/2 : ℝ)^(p.1+1) * (1/2 : ℝ)^(p.2+1)) :=
      Summable.mul_of_nonneg
        (f := fun n : ℕ => (1/2 : ℝ)^(n+1))
        (g := fun n : ℕ => (1/2 : ℝ)^(n+1))
        hgeomshift hgeomshift (fun n => by positivity) (fun n => by positivity)
    refine hm.of_nonneg_of_le (fun p => hFnonneg p.1 p.2) ?_
    intro ⟨n,j⟩
    dsimp [F]
    calc
      (1/2 : ℝ)^(j+1) / ((j : ℝ)+2)^(n+1) / (n+1 : ℝ) ≤
          (1/2 : ℝ)^(j+1) / (2 : ℝ)^(n+1) / 1 := by
        gcongr
        · exact le_add_of_nonneg_left (Nat.cast_nonneg j)
        · have := Nat.cast_nonneg (α := ℝ) n; linarith
      _ = (1/2 : ℝ)^(n+1) * (1/2 : ℝ)^(j+1) := by
        simp only [inv_pow, div_eq_mul_inv, one_mul]
        ring
  have hG1double : G 1 = ∑' n : ℕ, ∑' j : ℕ, F n j := by
    dsimp [G]
    simp only [one_pow, mul_one]
    apply tsum_congr
    intro n
    rw [hrt (n+1) (by omega), ← tsum_div_const]
  have hrow (j : ℕ) : (∑' n : ℕ, F n j) =
      (Real.log ((j : ℝ)+2) - Real.log ((j : ℝ)+1)) / (2 : ℝ)^(j+1) := by
    have hj : (0 : ℝ) < (j : ℝ)+2 := by positivity
    have hx : |(1 : ℝ)/((j : ℝ)+2)| < 1 := by
      rw [abs_of_pos (by positivity)]
      apply (div_lt_one hj).mpr
      have := Nat.cast_nonneg (α := ℝ) j
      linarith
    have hlogs := (Real.hasSum_pow_div_log_of_abs_lt_one hx).mul_left ((1/2 : ℝ)^(j+1))
    have hident : (fun n : ℕ => F n j) =
        (fun n : ℕ => (1/2 : ℝ)^(j+1) * (((1 : ℝ)/((j : ℝ)+2))^(n+1)/(n+1 : ℝ))) := by
      funext n
      simp only [F, inv_pow, div_eq_mul_inv, one_mul]
      ring
    rw [hident, hlogs.tsum_eq]
    have hfrac : 1 - (1 : ℝ)/((j : ℝ)+2) = ((j : ℝ)+1)/((j : ℝ)+2) := by
      field_simp
      ring
    rw [hfrac, Real.log_div (by positivity) (by positivity), neg_sub]
    rw [div_pow, one_pow]
    ring
  have htel : (∑' j : ℕ, (Real.log ((j : ℝ)+2) - Real.log ((j : ℝ)+1)) /
      (2 : ℝ)^(j+1)) = ∑' j : ℕ, Real.log ((j : ℝ)+1)/(2 : ℝ)^(j+1) := by
    let L : ℕ → ℝ := fun j => Real.log ((j : ℝ)+1)/(2 : ℝ)^(j+1)
    have hL : Summable L := hlog
    have hLs : Summable (fun j : ℕ => L (j+1)) := (summable_nat_add_iff 1).mpr hL
    have hpoint (j : ℕ) :
        (Real.log ((j : ℝ)+2) - Real.log ((j : ℝ)+1))/(2 : ℝ)^(j+1) =
          2*L (j+1)-L j := by
      dsimp [L]
      push_cast
      have he : (j : ℝ)+1+1 = (j : ℝ)+2 := by ring
      rw [he, pow_succ (2 : ℝ) (j+1)]
      field_simp
    simp_rw [hpoint]
    rw [Summable.tsum_sub (hLs.mul_left 2) hL, tsum_mul_left]
    have hz : L 0 = 0 := by simp [L]
    have he := hL.tsum_eq_zero_add
    rw [hz, zero_add] at he
    rw [← he]
    dsimp only [L]
    ring
  have hG1 : G 1 = ∑' j : ℕ, Real.log ((j : ℝ)+1)/(2 : ℝ)^(j+1) := by
    have hswap := Summable.tsum_comm (f := F) hdouble
    rw [hG1double, ← hswap]
    simp_rw [hrow]
    exact htel
  have hvalue : (∑' n : ℕ, c n) = SomosConstant := by
    rw [hH1, hG1]
    rfl
  refine ⟨hkernel, hlog, ⟨a, ha, hu⟩, ?_⟩
  intro b hb
  rw [hu b hb]
  rw [← hvalue]
  exact ha_limit

end D5.S1.Recurrence.LerchSomosLimit
