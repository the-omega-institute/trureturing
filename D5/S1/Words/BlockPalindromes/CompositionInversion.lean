/- GID: D5/S1/Words/BlockPalindromes/CompositionInversion
   generality: G
   mirror-B: D5/B/S1/Words/BlockPalindromes/CompositionInversion
   mirror-E: none(waiver:gabrić-shallit-expected-width)
   anchors: []
   utility: none
   digest: Gabrić–Shallit Conjecture 5 and its greedy renewal/composition proof. -/

/- The alphabet is Fin k; bs lists blocks from the centre outwards.
   The empty word is assigned width zero. The source's Lemma 3 is not used.
   proof_shape: a274190=not-applicable (definition).
   proof_shape: a274190_zero_of_lt=bind-only.
     consumers: CompositionInversion.a274190_compCount, CompositionInversion.a274190_stable.
   proof_shape: a274190_stable=content. escape_witness: CompositionInversion.a274190_stable.
   proof_shape: a274190_diagonal_limit=content. escape_witness: CompositionInversion.a274190_stable.
     consumers: result.
   proof_shape: compCount=not-applicable (definition).
   proof_shape: compCount_one=content. escape_witness: CompositionInversion.compCount_one.
   proof_shape: compCount_full=bind-only.
     consumers: CompositionInversion.a274190_stable_compCount, CompositionInversion.compSeries_limit.
   proof_shape: compCount_bound_succ=bind-only.
     consumers: CompositionInversion.a274190_compCount.
   proof_shape: a274190_compCount=content. escape_witness: CompositionInversion.a274190_compCount.
   proof_shape: a274190_stable_compCount=content. escape_witness: CompositionInversion.a274190_compCount.
     consumers: stable_series_summable, stable_series_identity.
   proof_shape: compCount_fib_bound=content. escape_witness: CompositionInversion.compCount_fib_bound.
   proof_shape: fib_real_bound=bind-only.
     consumers: CompositionInversion.composition_series_summable.
   proof_shape: composition_series_summable=content. escape_witness: CompositionInversion.compCount_fib_bound.
     consumers: stable_series_summable, compSeries_limit, compTerm_summable, compSeries_le_total.
   proof_shape: compCount_le_full=bind-only.
     consumers: CompositionInversion.compTerm_le_full.
   proof_shape: compTerm=not-applicable (definition).
   proof_shape: compSeries=not-applicable (definition).
   proof_shape: totalSeries=not-applicable (definition).
   proof_shape: compTerm_nonneg=bind-only.
     consumers: CompositionInversion.compSeries_limit, CompositionInversion.compSeries_nonneg, CompositionInversion.compTerm_summable, CompositionInversion.totalSeries_nonneg.
   proof_shape: compTerm_le_full=bind-only.
     consumers: CompositionInversion.compSeries_le_total, CompositionInversion.compSeries_limit, CompositionInversion.compTerm_summable.
   proof_shape: compTerm_summable=content. escape_witness: CompositionInversion.compCount_fib_bound.
     consumers: compSeries_le_total, shiftedComp_summable.
   proof_shape: compSeries_nonneg=bind-only.
     consumers: CompositionInversion.cCoeff_nonneg.
   proof_shape: totalSeries_nonneg=bind-only.
     consumers: CompositionInversion.cCoeff_summable.
   proof_shape: compSeries_le_total=content. escape_witness: CompositionInversion.compCount_fib_bound.
     consumers: cCoeff_summable.
   proof_shape: cCoeff=not-applicable (definition).
   proof_shape: cCoeff_nonneg=bind-only.
     consumers: CompositionInversion.cCoeff_summable, CompositionInversion.unbordered_composition_series.
   proof_shape: cCoeff_summable=content. escape_witness: CompositionInversion.compCount_fib_bound.
     consumers: unbordered_composition_series, totalSeries_firstpart.
   proof_shape: shiftedComp=not-applicable (definition).
   proof_shape: shiftedComp_add=bind-only.
     consumers: CompositionInversion.shiftedComp_summable, CompositionInversion.shiftedComp_tsum.
   proof_shape: shiftedComp_summable=content. escape_witness: CompositionInversion.compCount_fib_bound.
     consumers: compSeries_firstpart, shiftedComp_tsum.
   proof_shape: shiftedComp_tsum=content. escape_witness: CompositionInversion.compCount_fib_bound.
     consumers: compSeries_firstpart.
   proof_shape: compCount_firstpart=bind-only.
     consumers: CompositionInversion.compSeries_firstpart.
   proof_shape: compSeries_firstpart=content. escape_witness: CompositionInversion.compSeries_firstpart.
   proof_shape: compSeries_limit=content. escape_witness: CompositionInversion.compCount_fib_bound.
     consumers: totalSeries_firstpart.
   proof_shape: totalSeries_firstpart=content. escape_witness: CompositionInversion.compCount_fib_bound.
     consumers: unbordered_composition_series.
   proof_shape: series_pairing_identity=bind-only.
     consumers: CompositionInversion.unbordered_composition_series.
   proof_shape: unbordered_composition_series=content. escape_witness: CompositionInversion.unbordered_composition_series.
   escape_witness: unbordered_composition_series
   admission_basis: escape-witness
   Direct frozen dependencies: D5/S0/Computability/Coding/DepthBudgetIidGreedyOptimality.words
     statement_id: sha256:ac39f4d6ac85644b4d36960e026f51c85dafd409386991d3defafb1ebead5aa6.
   The frozen words declaration above is used by:
     unbordered_composition_series.
   Direct frozen dependencies of all other declarations: none.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15783
   DTR reading: DTR-Unregistered (Observe) for all 7 public theorem audit targets.
   Missing evidence: source-bound dependent-family variation, sensitivity,
   observational dependence, and a compiled enrolled four-slot registration.
-/

import D5.S1.Words.BlockPalindromes.GreedyRenewal
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.Real.GoldenRatio
open scoped BigOperators
open Set Finset Filter Topology
open D5.S1.Words.BlockPalindromes.GreedyRenewal
namespace D5.S1.Words.BlockPalindromes.CompositionInversion

def a274190 : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, m + 1 => if m + 1 ≤ n + 1 then a274190 n m + a274190 n (2 * (m + 1)) else 0

private theorem a274190_zero_of_lt : ∀ N m : ℕ, N < m → a274190 N m = 0 := by
  intro N
  induction N with
  | zero => intro m hm; cases m with | zero => omega | succ m => rfl
  | succ N ih =>
    intro m hm
    cases m with
    | zero => omega
    | succ m =>
      rw [a274190.eq_3]
      have hfalse : ¬ m + 1 ≤ N + 1 := by omega
      simp [hfalse]

theorem a274190_stable : ∀ N d : ℕ, 2 * d ≤ N →
    a274190 N (N - d) = a274190 (2 * d) d := by
  intro N
  induction N with
  | zero =>
    intro d hd
    have hd0 : d = 0 := by omega
    subst d
    rfl
  | succ N ih =>
    intro d hd
    by_cases heq : N + 1 = 2 * d
    · have hsub : N + 1 - d = d := by omega
      rw [hsub,heq]
    · have hn : 2 * d ≤ N := by omega
      have hm : N + 1 - d = (N - d) + 1 := by omega
      rw [hm,a274190.eq_3,if_pos (by omega),a274190_zero_of_lt N (2 * ((N - d) + 1)) (by omega)]
      simpa only [Nat.add_zero] using ih d hn

theorem a274190_diagonal_limit (d : ℕ) :
    Tendsto (fun N : ℕ => (a274190 N (N - d) : ℝ)) atTop
      (𝓝 (a274190 (2 * d) d : ℝ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (2 * d)] with N hN
  rw [a274190_stable N d hN]



def compCount : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, b => ∑ i ∈ Finset.range (n + 1),
      if i + 1 ≤ b then compCount (n - i) (2 * i + 1) else 0
termination_by n => n

private theorem compCount_one (n : ℕ) : compCount n 1 = 1 := by
  induction n with
  | zero => simp only [compCount.eq_1]
  | succ n ih =>
    rw [compCount.eq_2,Finset.sum_eq_single 0]
    · simpa using ih
    · intro i hi hi0
      have hn : ¬ i + 1 ≤ 1 := by omega
      simp [hn]
    · simp

private lemma compCount_full (n b : ℕ) (hn : n ≤ b) : compCount n b = compCount n n := by
  cases n with
  | zero => simp only [compCount.eq_1]
  | succ n =>
    rw [compCount.eq_2,compCount.eq_2]
    apply Finset.sum_congr rfl
    intro i hi
    have hin := Finset.mem_range.mp hi
    rw [if_pos (by omega),if_pos (by omega)]

private lemma compCount_bound_succ (n b : ℕ) : compCount n (b + 1) = compCount n b +
    if b < n then compCount (n - (b + 1)) (2 * b + 1) else 0 := by
  cases n with
  | zero => simp only [compCount.eq_1,Nat.not_lt_zero,if_false,Nat.add_zero]
  | succ n =>
    rw [compCount.eq_2,compCount.eq_2]
    have ht (i : ℕ) :
        (if i + 1 ≤ b + 1 then compCount (n - i) (2 * i + 1) else 0) =
        (if i + 1 ≤ b then compCount (n - i) (2 * i + 1) else 0) +
        (if i = b then compCount (n - b) (2 * b + 1) else 0) := by
      by_cases he : i = b
      · subst i
        simp
      · by_cases hl : i + 1 ≤ b
        · simp [hl,he,Nat.le_trans hl (Nat.le_succ b)]
        · have hfalse : ¬ i + 1 ≤ b + 1 := by omega
          simp [hl,he,hfalse]
    rw [Finset.sum_congr rfl (fun i _ => ht i),Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',Finset.mem_range]
    have hs : n + 1 - (b + 1) = n - b := by omega
    rw [hs]



lemma a274190_compCount : ∀ N m : ℕ, m ≤ N →
    a274190 N m = compCount (N - m) (m + 1) := by
  intro N
  induction N with
  | zero =>
    intro m hm
    have hm0 : m = 0 := by omega
    subst m
    simp only [Nat.sub_self,Nat.zero_add,a274190.eq_1,compCount.eq_1]
  | succ N ih =>
    intro m hm
    cases m with
    | zero => simp only [a274190.eq_1,Nat.sub_zero,Nat.zero_add,compCount_one]
    | succ m =>
      have hNm : m ≤ N := by omega
      have hd : N + 1 - (m + 1) = N - m := by omega
      rw [a274190.eq_3,if_pos hm,ih m hNm,hd,compCount_bound_succ (N - m) (m + 1)]
      by_cases hhi : 2 * (m + 1) ≤ N
      · rw [ih _ hhi,if_pos (by omega)]
        have hs : N - 2 * (m + 1) = N - m - (m + 1 + 1) := by omega
        rw [hs]
      · rw [a274190_zero_of_lt _ _ (by omega),if_neg (by omega)]

lemma a274190_stable_compCount (d : ℕ) :
    a274190 (2 * d) d = compCount d d := by
  rw [a274190_compCount _ _ (by omega)]
  have hs : 2 * d - d = d := by omega
  rw [hs,compCount_full _ _ (by omega)]

lemma compCount_fib_bound : ∀ n b : ℕ, compCount n b ≤ Nat.fib (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro b
    cases n with
    | zero => simp only [compCount.eq_1,Nat.zero_add,Nat.fib_one]; exact le_rfl
    | succ n =>
      rw [compCount.eq_2,Finset.sum_range_succ']
      have hfirst : (if 0 + 1 ≤ b then compCount (n - 0) (2 * 0 + 1) else 0) ≤ 1 := by
        simp only [Nat.zero_add,Nat.sub_zero,Nat.mul_zero,compCount_one]
        split_ifs <;> omega
      have hterms :
          (∑ i ∈ Finset.range n, if i + 1 + 1 ≤ b then compCount (n - (i + 1)) (2 * (i + 1) + 1) else 0) ≤
          ∑ i ∈ Finset.range n, Nat.fib (n - i) := by
        apply Finset.sum_le_sum
        intro i hi
        have hin := Finset.mem_range.mp hi
        split_ifs with hb
        · have hp := ih (n - (i + 1)) (by omega) (2 * (i + 1) + 1)
          have he : n - (i + 1) + 1 = n - i := by omega
          simpa only [he] using hp
        · exact Nat.zero_le _
      have hsum : (∑ i ∈ Finset.range n, Nat.fib (n - i)) =
          ∑ i ∈ Finset.range (n + 1), Nat.fib i := by
        rw [← Finset.sum_range_reflect Nat.fib (n + 1),Finset.sum_range_succ]
        simp only [Nat.add_sub_cancel,Nat.sub_self,Nat.fib_zero,Nat.add_zero]
      have hf := Nat.fib_succ_eq_succ_sum (n + 1)
      omega

private lemma fib_real_bound (n : ℕ) : (Nat.fib (n + 1) : ℝ) ≤ (7 / 4 : ℝ)^n := by
  have h := Real.goldenRatio_mul_fib_succ_add_fib n
  rw [pow_succ] at h
  have hfirst : (Nat.fib (n + 1) : ℝ) ≤ Real.goldenRatio ^ n := by
    nlinarith [Real.goldenRatio_pos, Nat.cast_nonneg (α := ℝ) (Nat.fib n)]
  have hphi : Real.goldenRatio ≤ (7 / 4 : ℝ) := by
    nlinarith [Real.goldenRatio_sq, Real.goldenRatio_pos]
  exact hfirst.trans (pow_le_pow_left₀ Real.goldenRatio_pos.le hphi n)

theorem composition_series_summable {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun d : ℕ => (compCount d d : ℝ) / (k : ℝ)^d) := by
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hratio : 7 / 4 / (k : ℝ) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  apply Summable.of_nonneg_of_le (fun d => by positivity) _
    (summable_geometric_of_lt_one (by positivity) hratio)
  intro d
  rw [div_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (Nat.cast_le.mpr (compCount_fib_bound d d)).trans (fib_real_bound d)




private lemma compCount_le_full (n b : ℕ) : compCount n b ≤ compCount n n := by
  cases n with
  | zero => simp only [compCount.eq_1]; exact le_rfl
  | succ n =>
    rw [compCount.eq_2,compCount.eq_2]
    apply Finset.sum_le_sum
    intro i hi
    have hin := Finset.mem_range.mp hi
    rw [if_pos (by omega : i + 1 ≤ n + 1)]
    split_ifs <;> omega

noncomputable def compTerm (k b d : ℕ) : ℝ := (compCount d b : ℝ) / (k : ℝ)^d
private noncomputable def compSeries (k b : ℕ) : ℝ := ∑' d : ℕ, compTerm k b d
noncomputable def totalSeries (k : ℕ) : ℝ := ∑' d : ℕ, compTerm k d d

private lemma compTerm_nonneg (k b d : ℕ) : 0 ≤ compTerm k b d := by unfold compTerm; positivity
private lemma compTerm_le_full (k b d : ℕ) : compTerm k b d ≤ compTerm k d d := by
  unfold compTerm
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (compCount_le_full d b)) (by positivity)
private lemma compTerm_summable {k : ℕ} (hk : 2 ≤ k) (b : ℕ) : Summable (compTerm k b) := by
  exact Summable.of_nonneg_of_le (compTerm_nonneg k b) (compTerm_le_full k b)
    (composition_series_summable hk)
private lemma compSeries_nonneg (k b : ℕ) : 0 ≤ compSeries k b := tsum_nonneg (compTerm_nonneg _ _)
private lemma totalSeries_nonneg (k : ℕ) : 0 ≤ totalSeries k := tsum_nonneg (fun d => compTerm_nonneg _ _ _)
private lemma compSeries_le_total {k : ℕ} (hk : 2 ≤ k) (b : ℕ) : compSeries k b ≤ totalSeries k := by
  exact Summable.tsum_le_tsum (compTerm_le_full k b) (compTerm_summable hk b) (composition_series_summable hk)

private noncomputable def cCoeff (k i : ℕ) : ℝ :=
  if i = 0 then 0 else compSeries k (2 * i - 1) / (k : ℝ)^i
private lemma cCoeff_nonneg (k i : ℕ) : 0 ≤ cCoeff k i := by
  unfold cCoeff
  split_ifs
  · exact le_rfl
  · exact div_nonneg (compSeries_nonneg _ _) (by positivity)
private lemma cCoeff_summable {k : ℕ} (hk : 2 ≤ k) : Summable (cCoeff k) := by
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hx : 1 / (k : ℝ) < 1 := by rw [div_lt_one (by positivity)]; linarith
  apply Summable.of_nonneg_of_le (cCoeff_nonneg k) _
    ((summable_geometric_of_lt_one (by positivity) hx).mul_left (totalSeries k))
  intro i
  unfold cCoeff
  split_ifs with hi
  · exact mul_nonneg (totalSeries_nonneg _) (by positivity)
  · rw [one_div_pow, mul_one_div]
    exact div_le_div_of_nonneg_right (compSeries_le_total hk _) (by positivity)

private noncomputable def shiftedComp (k p b n : ℕ) : ℝ :=
  if p ≤ n then (compCount (n - p) b : ℝ) / (k : ℝ)^n else 0
private lemma shiftedComp_add (k p b n : ℕ) : shiftedComp k p b (n + p) = compTerm k b n / (k : ℝ)^p := by
  simp only [shiftedComp, Nat.le_add_left,if_true,Nat.add_sub_cancel,pow_add,compTerm]
  ring
private lemma shiftedComp_summable {k : ℕ} (hk : 2 ≤ k) (p b : ℕ) : Summable (shiftedComp k p b) := by
  apply (summable_nat_add_iff p).mp
  simpa only [shiftedComp_add] using (compTerm_summable hk b).div_const ((k : ℝ)^p)
private lemma shiftedComp_tsum {k : ℕ} (hk : 2 ≤ k) (p b : ℕ) :
    (∑' n : ℕ, shiftedComp k p b n) = compSeries k b / (k : ℝ)^p := by
  have he := (shiftedComp_summable hk p b).sum_add_tsum_nat_add p
  have hzero : (∑ n ∈ Finset.range p, shiftedComp k p b n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnp : ¬ p ≤ n := by have := Finset.mem_range.mp hn; omega
    simp [shiftedComp,hnp]
  rw [hzero,zero_add] at he
  simpa only [shiftedComp_add,tsum_div_const,compSeries] using he.symm

private lemma compCount_firstpart (n b : ℕ) : compCount n b = (if n = 0 then 1 else 0) +
    ∑ p ∈ Finset.Icc 1 b, if p ≤ n then compCount (n - p) (2 * p - 1) else 0 := by
  cases n with
  | zero =>
    simp only [compCount.eq_1,if_true]
    have hz : (∑ p ∈ Finset.Icc 1 b, if p ≤ 0 then compCount (0 - p) (2 * p - 1) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have hp0 : ¬ p ≤ 0 := by have := (Finset.mem_Icc.mp hp).1; omega
      simp [hp0]
    rw [hz,Nat.add_zero]
  | succ n =>
    rw [compCount.eq_2,if_neg (by omega),zero_add]
    rw [Finset.sum_ite,Finset.sum_ite]
    simp only [Finset.sum_const_zero,Nat.add_zero]
    apply Finset.sum_bij (fun i _ => i + 1)
    · intro i hi
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc] at *
      omega
    · intro i hi j hj he
      omega
    · intro p hp
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc] at *
      refine ⟨p - 1,?_,?_⟩ <;> omega
    · intro i hi
      congr 1 <;> omega

private lemma compSeries_firstpart {k : ℕ} (hk : 2 ≤ k) (b : ℕ) :
    compSeries k b = 1 + ∑ p ∈ Finset.Icc 1 b, cCoeff k p := by
  have hpoint (n : ℕ) : compTerm k b n = (if n = 0 then 1 else 0) +
      ∑ p ∈ Finset.Icc 1 b, shiftedComp k p (2 * p - 1) n := by
    unfold compTerm
    rw [compCount_firstpart]
    push_cast
    rw [add_div,Finset.sum_div]
    congr 1
    · by_cases hn : n = 0
      · subst n; simp
      · simp [hn]
    · apply Finset.sum_congr rfl
      intro p hp
      by_cases hpn : p ≤ n <;> simp [shiftedComp,hpn]
  rw [compSeries,tsum_congr hpoint]
  rw [Summable.tsum_add (hasSum_ite_eq 0 (1 : ℝ)).summable (summable_sum (fun p _ => shiftedComp_summable hk p (2 * p - 1)))]
  rw [Summable.tsum_finsetSum (fun p _ => shiftedComp_summable hk p (2 * p - 1))]
  simp only [tsum_ite_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : p ≠ 0 := by have := (Finset.mem_Icc.mp hp).1; omega
  rw [shiftedComp_tsum hk,cCoeff,if_neg hp0]


private lemma compSeries_limit {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (compSeries k) atTop (𝓝 (totalSeries k)) := by
  have hp (d : ℕ) : Tendsto (fun b => compTerm k b d) atTop (𝓝 (compTerm k d d)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop d] with b hb
    simp only [compTerm,compCount_full d b hb]
  have hb : ∀ᶠ b : ℕ in atTop, ∀ d : ℕ, ‖compTerm k b d‖ ≤ compTerm k d d := by
    apply Filter.Eventually.of_forall
    intro b d
    rw [Real.norm_eq_abs,abs_of_nonneg (compTerm_nonneg _ _ _)]
    exact compTerm_le_full _ _ _
  exact tendsto_tsum_of_dominated_convergence (composition_series_summable hk) hp hb

private lemma totalSeries_firstpart {k : ℕ} (hk : 2 ≤ k) :
    totalSeries k = 1 + ∑' i : ℕ, cCoeff k i := by
  have hsum := (cCoeff_summable hk).hasSum.tendsto_sum_nat
  have hshift := hsum.comp (tendsto_add_atTop_nat 1)
  have hfn (b : ℕ) : (∑ i ∈ Finset.range (b + 1), cCoeff k i) =
      ∑ i ∈ Finset.Icc 1 b, cCoeff k i := by
    have hset : Finset.range (b + 1) = insert 0 (Finset.Icc 1 b) := by
      ext i
      simp only [Finset.mem_range,Finset.mem_insert,Finset.mem_Icc]
      omega
    rw [hset,Finset.sum_insert (by simp)]
    simp [cCoeff]
  have ht : Tendsto (fun b => 1 + ∑ i ∈ Finset.Icc 1 b, cCoeff k i) atTop
      (𝓝 (1 + ∑' i : ℕ, cCoeff k i)) := by
    simpa only [Function.comp_def,hfn] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hshift
  have heq : (fun b => 1 + ∑ i ∈ Finset.Icc 1 b, cCoeff k i) = compSeries k := by
    funext b
    exact (compSeries_firstpart hk b).symm
  rw [heq] at ht
  exact tendsto_nhds_unique (compSeries_limit hk) ht



set_option maxHeartbeats 1000000 in
private theorem series_pairing_identity (B C : ℕ → ℝ) (hB : Summable B) (hC : Summable C)
    (hBn : ∀ i, 0 ≤ B i) (hCn : ∀ i, 0 ≤ C i) (hB0 : B 0 = 0) (hC0 : C 0 = 0)
    (hrec : ∀ i, B i * (1 + ∑ j ∈ Finset.Icc 1 (2 * i - 1), C j) =
      C i - C i * ∑ j ∈ Finset.Icc 1 (i / 2), B j) :
    (∑' i : ℕ, B i) * (1 + ∑' i : ℕ, C i) = ∑' i : ℕ, C i := by
  classical
  let small : ℕ × ℕ → ℝ := fun p => if p.2 < 2 * p.1 then B p.1 * C p.2 else 0
  let large : ℕ × ℕ → ℝ := fun p => if 2 * p.1 ≤ p.2 then B p.1 * C p.2 else 0
  have hprod := hB.mul_of_nonneg hC hBn hCn
  have hs : Summable small := by
    apply Summable.of_nonneg_of_le _ _ hprod
    · intro p
      unfold small
      split_ifs <;> first | exact mul_nonneg (hBn _) (hCn _) | exact le_rfl
    · intro p
      unfold small
      split_ifs <;> first | exact le_rfl | exact mul_nonneg (hBn _) (hCn _)
  have hl : Summable large := by
    apply Summable.of_nonneg_of_le _ _ hprod
    · intro p
      unfold large
      split_ifs <;> first | exact mul_nonneg (hBn _) (hCn _) | exact le_rfl
    · intro p
      unfold large
      split_ifs <;> first | exact le_rfl | exact mul_nonneg (hBn _) (hCn _)
  have hsmall (i : ℕ) : (∑' j : ℕ, small (i,j)) =
      B i * ∑ j ∈ Finset.Icc 1 (2 * i - 1), C j := by
    rw [tsum_eq_sum (s := Finset.Icc 1 (2 * i - 1))]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hlt : j < 2 * i := by have := Finset.mem_Icc.mp hj; omega
      simp only [small,if_pos hlt]
    · intro j hj
      by_cases hj0 : j = 0
      · subst j
        simp [small,hC0]
      · have hfalse : ¬ j < 2 * i := by
          simp only [Finset.mem_Icc] at hj
          omega
        simp only [small,if_neg hfalse]
  have hlarge (j : ℕ) : (∑' i : ℕ, large (i,j)) =
      C j * ∑ i ∈ Finset.Icc 1 (j / 2), B i := by
    rw [tsum_eq_sum (s := Finset.Icc 1 (j / 2))]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hle : 2 * i ≤ j := by have := Finset.mem_Icc.mp hi; omega
      change (if 2 * i ≤ j then B i * C j else 0) = C j * B i
      rw [if_pos hle,mul_comm]
    · intro i hi
      by_cases hi0 : i = 0
      · subst i
        simp [large,hB0]
      · have hfalse : ¬ 2 * i ≤ j := by
          simp only [Finset.mem_Icc] at hi
          omega
        simp only [large,if_neg hfalse]
  have hpoint (i : ℕ) : B i + (∑' j : ℕ, small (i,j)) = C i - (∑' j : ℕ, large (j,i)) := by
    rw [hsmall,hlarge]
    nlinarith [hrec i]
  have he : (∑' i : ℕ, (B i + (∑' j : ℕ, small (i,j)))) =
      (∑' i : ℕ, (C i - (∑' j : ℕ, large (j,i)))) := tsum_congr hpoint
  have hls : Summable (fun i : ℕ => ∑' j : ℕ, large (j,i)) := hl.prod_symm.prod
  rw [hB.tsum_add hs.prod,hC.tsum_sub hls] at he
  have hcomm : (∑' j : ℕ, ∑' i : ℕ, large (i,j)) =
      (∑' i : ℕ, ∑' j : ℕ, large (i,j)) := hl.tsum_comm
  rw [← hs.tsum_prod,hcomm,← hl.tsum_prod] at he
  have hsplit (p : ℕ × ℕ) : small p + large p = B p.1 * C p.2 := by
    unfold small large
    by_cases hp : p.2 < 2 * p.1
    · have hn : ¬ 2 * p.1 ≤ p.2 := by omega
      simp [hp,hn]
    · have hle : 2 * p.1 ≤ p.2 := by omega
      simp [hp,hle]
  have ht := hB.tsum_mul_tsum hC hprod
  rw [← tsum_congr hsplit,hs.tsum_add hl] at ht
  nlinarith

theorem unbordered_composition_series {k : ℕ} (hk : 2 ≤ k) :
    totalSeries k = 1 / (1 - q k (uCount k)) := by
  have hrec (i : ℕ) : qCoeff k i * (1 + ∑ j ∈ Finset.Icc 1 (2 * i - 1), cCoeff k j) =
      cCoeff k i - cCoeff k i * ∑ j ∈ Finset.Icc 1 (i / 2), qCoeff k j := by
    by_cases hi0 : i = 0
    · subst i
      simp [qCoeff,cCoeff]
    · rw [qCoeff_recurrence hk i (by omega),cCoeff,if_neg hi0,compSeries_firstpart hk]
      ring
  have he := series_pairing_identity (qCoeff k) (cCoeff k) (qCoeff_summable hk)
    (cCoeff_summable hk) (qCoeff_nonneg k) (cCoeff_nonneg k)
    (by simp [qCoeff]) (by simp [cCoeff]) hrec
  rw [tsum_qCoeff hk,← totalSeries_firstpart hk] at he
  have hf := totalSeries_firstpart hk
  have hq := unbordered_q_lt_one hk
  apply (eq_div_iff (ne_of_gt (sub_pos.mpr hq))).mpr
  nlinarith



end D5.S1.Words.BlockPalindromes.CompositionInversion
