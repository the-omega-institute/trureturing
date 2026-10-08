/- GID: D5/S1/Words/Forbidden/ForbiddenWordGrowth
   generality: G
   mirror-B: D5/B/S1/Words/Forbidden/ForbiddenWordGrowth
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Avoidance growth and escaping weighted averages control the boundary limit. -/
/-
proof_shape: avoidOnes_bounds: bind-only; consumers: rho_nonneg, rho_le_one, realImbalanceSeries_summable
proof_shape: avoidCount_pos: bind-only; consumer: log_avoidCount_subadditive
proof_shape: avoidCount_ge_one: bind-only; consumer: log_avoidCount_div_bddBelow
proof_shape: words_card_le: bind-only; consumer: growthRate_lt_two
proof_shape: avoidCount_submultiplicative: content
proof_shape: log_avoidCount_subadditive: bind-only; consumer: growthRate
proof_shape: log_avoidCount_div_bddBelow: bind-only; consumer: growthLog_tendsto
proof_shape: growthLog_tendsto: bind-only; consumer: avoidCount_eventually_le_power
proof_shape: growthRate_lower_power: bind-only; consumer: countSeriesEval_ge_geometric
proof_shape: growthRate_lt_two: content
proof_shape: avoidCount_eventually_le_power: content
proof_shape: weighted_avoidCount_summable: content
proof_shape: avoidCount_summable: bind-only; consumer: realCountSeries_summable
proof_shape: weighted_tsum_error_bound: bind-only; consumer: weighted_tsum_tendsto
proof_shape: weighted_tsum_tendsto: content
escape_witness: avoidCount_submultiplicative on result's live proof path.
admission_basis: escape-witness
Direct frozen dependencies: none on the protected baseline.
Same-delivery dependencies: ForbiddenWordCounting.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S1.Words.Forbidden.ForbiddenWordCounting
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Finset
open scoped Topology

namespace D5.S1.Words.Forbidden.ForbiddenWordGrowth
open D5.S1.Words.Forbidden.ForbiddenWordCounting

noncomputable def avoidCount (w : List Bool) (m : ℕ) : ℝ := (omega w m).card

theorem avoidCount_pos {w : List Bool} (hw : w ≠ []) (m : ℕ) : 0 < avoidCount w m := by
  unfold avoidCount
  exact_mod_cast card_pos.mpr (omega_nonempty hw m)

private theorem avoidCount_ge_one {w : List Bool} (hw : w ≠ []) (m : ℕ) : 1 ≤ avoidCount w m := by
  unfold avoidCount
  exact_mod_cast (by have hh := card_pos.mpr (omega_nonempty hw m); omega : 1 ≤ (omega w m).card)

private theorem words_card_le (m : ℕ) : (words m).card ≤ 2^m := by
  calc
    _ ≤ (Finset.univ : Finset (Fin m → Bool)).card := Finset.card_image_le
    _ = 2 ^ m := by simp

theorem avoidCount_submultiplicative (w : List Bool) (m n : ℕ) :
    avoidCount w (m+n) ≤ avoidCount w m*avoidCount w n := by
  classical
  have hcard : (omega w (m+n)).card ≤ ((omega w m) ×ˢ (omega w n)).card := by
    apply card_le_card_of_injOn (fun u => (u.take m,u.drop m))
    · intro u hu
      obtain ⟨hlen,ha⟩ := mem_omega.mp hu
      apply mem_product.mpr
      constructor
      · apply mem_omega.mpr
        refine ⟨List.length_take_of_le (by omega),?_⟩
        intro hit
        exact ha (hit.trans (List.take_prefix _ _).isInfix)
      · apply mem_omega.mpr
        refine ⟨by simp [hlen],?_⟩
        intro hit
        exact ha (hit.trans (List.drop_suffix _ _).isInfix)
    · intro u _ v _ he
      have ht := congrArg Prod.fst he
      have hd := congrArg Prod.snd he
      dsimp only at ht hd
      rw [← List.take_append_drop m u,← List.take_append_drop m v,ht,hd]
  rw [card_product] at hcard
  unfold avoidCount
  exact_mod_cast hcard

theorem log_avoidCount_subadditive {w : List Bool} (hw : w ≠ []) :
    Subadditive (fun m => Real.log (avoidCount w m)) := by
  intro m n
  have hp := avoidCount_pos hw (m+n)
  have hm := avoidCount_pos hw m
  have hn := avoidCount_pos hw n
  calc
    _ ≤ Real.log (avoidCount w m*avoidCount w n) :=
      Real.log_le_log hp (avoidCount_submultiplicative w m n)
    _ = _ := Real.log_mul hm.ne' hn.ne'

private theorem log_avoidCount_div_bddBelow {w : List Bool} (hw : w ≠ []) :
    BddBelow (Set.range fun m : ℕ => Real.log (avoidCount w m)/(m:ℝ)) := by
  refine ⟨0,?_⟩
  rintro x ⟨m,rfl⟩
  exact div_nonneg (Real.log_nonneg (avoidCount_ge_one hw m)) (Nat.cast_nonneg m)

noncomputable def growthRate (w : List Bool) (hw : w ≠ []) : ℝ := Real.exp ((log_avoidCount_subadditive hw).lim)

private theorem growthLog_tendsto {w : List Bool} (hw : w ≠ []) :
    Tendsto (fun m => Real.log (avoidCount w m)/(m:ℝ)) atTop (𝓝 ((log_avoidCount_subadditive hw).lim)) :=
  (log_avoidCount_subadditive hw).tendsto_lim (log_avoidCount_div_bddBelow hw)

theorem growthRate_lower_power {w : List Bool} (hw : w ≠ []) (m : ℕ) :
    growthRate w hw^m ≤ avoidCount w m := by
  by_cases hm : m=0
  · subst m
    simpa using avoidCount_ge_one hw 0
  · have hle := (log_avoidCount_subadditive hw).lim_le_div (log_avoidCount_div_bddBelow hw) hm
    have hmp : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hh : (log_avoidCount_subadditive hw).lim*(m:ℝ) ≤ Real.log (avoidCount w m) := (le_div_iff₀ hmp).mp hle
    have he := Real.exp_le_exp.mpr hh
    unfold growthRate
    simpa [mul_comm,Real.exp_nat_mul,Real.exp_log (avoidCount_pos hw m)] using he

theorem growthRate_lt_two {w : List Bool} (hw : w ≠ []) : growthRate w hw < 2 := by
  have hn : 0 < w.length := List.length_pos_iff.mpr hw
  have hcard : (omega w w.length).card < 2^w.length := by
    have hsub : omega w w.length ⊂ words w.length := by
      apply ssubset_iff_subset_ne.mpr
      refine ⟨filter_subset _ _,?_⟩
      intro he
      have hmem : w ∈ words w.length := mem_words.mpr rfl
      rw [← he] at hmem
      exact (mem_omega.mp hmem).2 List.infix_rfl
    exact (card_lt_card hsub).trans_le (words_card_le w.length)
  have hac : avoidCount w w.length < (2:ℝ)^w.length := by unfold avoidCount; exact_mod_cast hcard
  have hlog : Real.log (avoidCount w w.length) < (w.length:ℝ)*Real.log 2 := by
    have hh := Real.log_lt_log (avoidCount_pos hw _) hac
    simpa [Real.log_pow,mul_comm] using hh
  have hnr : (0:ℝ) < w.length := by exact_mod_cast hn
  have hL := (log_avoidCount_subadditive hw).lim_le_div (log_avoidCount_div_bddBelow hw) hn.ne'
  have hlt : (log_avoidCount_subadditive hw).lim < Real.log 2 := hL.trans_lt ((div_lt_iff₀ hnr).mpr (by simpa [mul_comm] using hlog))
  have he := Real.exp_lt_exp.mpr hlt
  simpa [growthRate,Real.exp_log (by norm_num : (0:ℝ) < 2)] using he

private theorem avoidCount_eventually_le_power {w : List Bool} (hw : w ≠ []) {s : ℝ}
    (hs : growthRate w hw < s) : ∀ᶠ m in atTop, avoidCount w m ≤ s^m := by
  have hp : 0 < growthRate w hw := Real.exp_pos _
  have hsp : 0 < s := hp.trans hs
  have hlog : (log_avoidCount_subadditive hw).lim < Real.log s := by
    have hh := Real.log_lt_log hp hs
    simpa [growthRate,Real.log_exp] using hh
  filter_upwards [(growthLog_tendsto hw).eventually (gt_mem_nhds hlog),
    eventually_gt_atTop (0:ℕ)] with m hm hm0
  have hmr : (0:ℝ) < m := by exact_mod_cast hm0
  have hmul : Real.log (avoidCount w m) ≤ (m:ℝ)*Real.log s :=
    by simpa [mul_comm] using ((div_lt_iff₀ hmr).mp hm).le
  have he := Real.exp_le_exp.mpr hmul
  simpa [Real.exp_log (avoidCount_pos hw m),Real.exp_nat_mul,Real.exp_log hsp] using he

theorem weighted_avoidCount_summable {w : List Bool} (hw : w ≠ []) (q : ℕ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : growthRate w hw*x<1) :
    Summable (fun m : ℕ => (m:ℝ)^q*avoidCount w m*x^m) := by
  by_cases hxzero : x=0
  · subst x
    apply summable_of_ne_finset_zero (s := {0})
    intro m hm
    have hm0 : m≠0 := by simpa using hm
    simp [zero_pow hm0]
  · have hxp : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxzero)
    have hdiv : growthRate w hw < 1/x := (lt_div_iff₀ hxp).mpr hx
    obtain ⟨s,hsrate,hsx⟩ := exists_between hdiv
    have hsp : 0 < s := (Real.exp_pos _).trans hsrate
    have hsprod : s*x<1 := (lt_div_iff₀ hxp).mp hsx
    have hnorm : ‖s*x‖ < 1 := by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hsp.le hx0)]
      exact hsprod
    apply Summable.of_norm_bounded_eventually_nat
      (summable_pow_mul_geometric_of_norm_lt_one q hnorm)
    filter_upwards [avoidCount_eventually_le_power hw hsrate] with m hm
    have hactual : 0 ≤ (m:ℝ)^q*avoidCount w m*x^m := by
      exact mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg m) q) (avoidCount_pos hw m).le)
        (pow_nonneg hx0 m)
    rw [Real.norm_eq_abs,abs_of_nonneg hactual]
    calc
      _ ≤ (m:ℝ)^q*s^m*x^m := by gcongr
      _ = (m:ℝ)^q*(s*x)^m := by rw [mul_pow]; ring

theorem avoidCount_summable {w : List Bool} (hw : w ≠ []) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : growthRate w hw*x<1) :
    Summable (fun m : ℕ => avoidCount w m*x^m) := by
  simpa using weighted_avoidCount_summable hw 0 hx0 hx

private theorem weighted_tsum_error_bound (p u : ℕ → ℝ) (L B eps : ℝ) (N : ℕ)
    (hp : ∀ n, 0 ≤ p n) (hpsum : Summable p) (hB : 0 ≤ B) (heps : 0 ≤ eps)
    (huB : ∀ n, |u n-L| ≤ B) (hutail : ∀ n, N ≤ n → |u n-L| ≤ eps) :
    |∑' n, p n * (u n-L)| ≤ B*(∑ n ∈ range N, p n) + eps*(∑' n, p n) := by
  let head : ℕ → ℝ := fun n => if n ∈ range N then p n else 0
  have hheadsum : Summable head := summable_of_ne_finset_zero (s := range N) (by
    intro n hn
    simp only [head,if_neg hn])
  have hhead : (∑' n, head n) = ∑ n ∈ range N, p n := by
    rw [tsum_eq_sum (s := range N) (by intro n hn; simp only [head,if_neg hn])]
    apply sum_congr rfl
    intro n hn
    simp only [head,if_pos hn]
  have hg : HasSum (fun n => B*head n+eps*p n)
      (B*(∑ n ∈ range N, p n)+eps*(∑' n,p n)) := by
    simpa [hhead] using (hheadsum.hasSum.mul_left B).add (hpsum.hasSum.mul_left eps)
  have hb (n : ℕ) : ‖p n*(u n-L)‖ ≤ B*head n+eps*p n := by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hp n)]
    by_cases hn : n ∈ range N
    · simp only [head,if_pos hn]
      have hh := mul_le_mul_of_nonneg_left (huB n) (hp n)
      have he := mul_nonneg heps (hp n)
      nlinarith
    · have htail := hutail n (by simpa only [mem_range,not_lt] using hn)
      simp only [head,if_neg hn,mul_zero,zero_add]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left htail (hp n)
  simpa only [Real.norm_eq_abs] using tsum_of_norm_bounded hg hb


theorem weighted_tsum_tendsto {T : Type*} (F : Filter T) (p : T → ℕ → ℝ)
    (u : ℕ → ℝ) (L B : ℝ)
    (hp : ∀ t n, 0 ≤ p t n) (hpsum : ∀ t, Summable (p t))
    (hunit : ∀ t, ∑' n, p t n = 1)
    (hB : 0 ≤ B) (huB : ∀ n, |u n-L| ≤ B)
    (hu : Tendsto u atTop (𝓝 L))
    (hescape : ∀ N, Tendsto (fun t => ∑ n ∈ range N, p t n) F (𝓝 0)) :
    Tendsto (fun t => ∑' n, p t n*u n) F (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hu (eps/2) (by linarith)
  have hsmall : ∀ᶠ t in F, B*(∑ n ∈ range N,p t n)<eps/2 := by
    have ht := (hescape N).const_mul B
    have hlt := ht.eventually (gt_mem_nhds (show B*(0:ℝ)<eps/2 by simpa using half_pos heps))
    simpa using hlt
  filter_upwards [hsmall] with t ht
  have hdev : Summable (fun n => p t n*(u n-L)) :=
    Summable.of_norm_bounded ((hpsum t).mul_left B) (by
      intro n
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hp t n)]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (huB n) (hp t n))
  have heq : (∑' n,p t n*u n)-L = ∑' n,p t n*(u n-L) := by
    have hconst := (hpsum t).mul_right L
    have htotal : Summable (fun n => p t n*u n) := by
      have hh := hdev.add hconst
      convert hh using 1
      funext n
      ring
    calc
      _ = (∑' n,p t n*u n)-(∑' n,p t n*L) := by
        rw [tsum_mul_right,hunit t,one_mul]
      _ = ∑' n,(p t n*u n-p t n*L) := (htotal.tsum_sub hconst).symm
      _ = _ := by
        apply tsum_congr
        intro n
        ring
  rw [Real.dist_eq,heq]
  have hb := weighted_tsum_error_bound (p t) u L B (eps/2) N
    (hp t) (hpsum t) hB (by linarith) huB (by
      intro n hn
      have hh : |u n-L| < eps/2 := by simpa [Real.dist_eq] using hN n hn
      exact hh.le)
  rw [hunit t] at hb
  linarith

noncomputable def avoidOnes (w : List Bool) (m : ℕ) : ℝ :=
  ∑ u ∈ omega w m,(u.count true : ℝ)

theorem avoidOnes_bounds (w : List Bool) (m : ℕ) :
    0 ≤ avoidOnes w m ∧ avoidOnes w m ≤ (m:ℝ)*avoidCount w m := by
  refine ⟨by unfold avoidOnes; exact sum_nonneg fun u _ => Nat.cast_nonneg (u.count true),?_⟩
  unfold avoidOnes
  calc
    _ ≤ ∑ u ∈ omega w m,(m:ℝ) := by
      apply sum_le_sum
      intro u hu
      exact_mod_cast (List.count_le_length (a := true) (l := u)).trans_eq (mem_omega.mp hu).1
    _ = _ := by simp [avoidCount,mul_comm]

end D5.S1.Words.Forbidden.ForbiddenWordGrowth
