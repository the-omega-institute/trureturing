/- GID: D5/S3/Analytic/Lemniscates/CapacityOneAreaDecayRate
   generality: I
   mirror-B: D5/B/S3/Analytic/Lemniscates/CapacityOneAreaDecayRate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/Lemniscates/CapacityOneAreaDecayRate.claim; result=D5/S3/Analytic/Lemniscates/CapacityOneAreaDecayRate.result; claim=D5/S3/Analytic/Lemniscates/CapacityOneAreaDecayRate.claim
   digest: A unit disc with an isolated point has transfinite diameter one and admits area decay faster than both proposed rates. -/

/- result: proof_shape: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (#15381; Refuted)
   Direct frozen dependency: FeketeLemniscateAreaRefutation definitions.
   Definitions (proof_shape: not applicable):
   pointDiameter -> TransfiniteDiameterOne, pointDiameter_bounds;
   TransfiniteDiameterOne -> claim, diameter_one; minimalArea -> claim, minimalArea_bound;
   claim -> result; K -> tuple_norm, tuple_disc, pointDiameter_bounds, diameter_one, result;
   competitor -> competitor_mem, competitor_cover, area_upper; degreeSeq -> degreeSeq_tendsto,
   geometric_decay, no_reciprocal_bigO, subsequence_area_bound.
   Proofs (each proof_shape: bind-only; consumers after the arrow):
   norm_det_vandermonde -> tuple_vandermonde_upper;
   root_row_product -> roots_vandermonde_lower; roots_vandermonde_lower -> pointDiameter_bounds;
   tuple_norm, tuple_disc -> tuple_vandermonde_upper;
   tuple_vandermonde_upper -> tuple_sup_bdd, pointDiameter_bounds;
   tuple_sup_bdd -> pointDiameter_bounds; pointDiameter_bounds -> diameter_one;
   diameter_one -> result; competitor_mem -> subsequence_area_bound;
   competitor_cover -> area_upper; area_upper, minimalArea_bound -> subsequence_area_bound;
   degreeSeq_tendsto, geometric_decay -> no_reciprocal_bigO;
   reciprocal_nat_bigO_log, no_reciprocal_bigO, subsequence_area_bound -> result.
   Classification conservatively counts elementary norm, polynomial, determinant,
   measure and asymptotic library applications with normalization as bind-only.
   No helper is claimed as an escape witness. -/

import D5.S3.Analytic.Lemniscates.FeketeLemniscateAreaRefutation
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.KummerExtension
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.Lemmas

noncomputable section
open scoped BigOperators ENNReal Topology
open Set Filter Asymptotics MeasureTheory
open D5.S3.Analytic.Lemniscates.FeketeLemniscateAreaRefutation

namespace D5.S3.Analytic.Lemniscates.CapacityOneAreaDecayRate

/-- The `s`-point diameter `sup_{a ∈ K^s} (∏_{i<j} |a_i - a_j|)^{2/(s(s-1))}`. -/
def pointDiameter (K : Set ℂ) (s : ℕ) : ℝ :=
  (⨆ a : {a : Fin s → ℂ // ∀ i, a i ∈ K}, vandermonde a.1) ^
    ((2 : ℝ) / (s * (s - 1) : ℝ))

/-- Transfinite diameter one. -/
def TransfiniteDiameterOne (K : Set ℂ) : Prop :=
  Filter.Tendsto (pointDiameter K) Filter.atTop (nhds 1)

def minimalArea (K : Set ℂ) (n : ℕ) : ℝ≥0∞ :=
  ⨅ (p : Polynomial ℂ) (_ : InP K n p), lemniscateArea p

def claim : Prop :=
  ∀ K : Set ℂ, IsCompact K → K.Nonempty → TransfiniteDiameterOne K →
    (fun n : ℕ => (minimalArea K n).toReal) =Θ[Filter.atTop]
      (fun n : ℕ => 1 / (n : ℝ)) ∨
    (fun n : ℕ => (minimalArea K n).toReal) =Θ[Filter.atTop]
      (fun n : ℕ => 1 / Real.log n)

private def K : Set ℂ := Metric.closedBall 0 1 ∪ {4}


private lemma norm_det_vandermonde {s : ℕ} (a : Fin s → ℂ) :
    ‖(Matrix.vandermonde a).det‖ = vandermonde a := by
  rw [Matrix.det_vandermonde]
  simp only [norm_prod, vandermonde]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  exact norm_sub_rev _ _

private lemma root_row_product {s : ℕ} (hs : 0 < s) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ s)
    (i : Fin s) : (∏ j ∈ Finset.univ.erase i, ‖ζ ^ i.val - ζ ^ j.val‖) = s := by
  classical
  have hp : (Polynomial.X ^ s - 1 : Polynomial ℂ) =
      ∏ j : Fin s, (Polynomial.X - Polynomial.C (ζ ^ j.val)) := by
    simpa [← Fin.prod_univ_eq_prod_range] using
      (X_pow_sub_C_eq_prod hζ hs (one_pow s : (1:ℂ)^s = 1))
  have hi : (ζ ^ i.val)^s = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hder : (Polynomial.derivative (Polynomial.X^s - 1 : Polynomial ℂ)).eval (ζ^i.val) =
      ∏ j ∈ Finset.univ.erase i, (ζ^i.val - ζ^j.val) := by
    rw [hp, Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum]
    simp only [Polynomial.derivative_X_sub_C,
      mul_one, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    apply Finset.sum_eq_single i
    · intro b hb hbi
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hbi, Finset.mem_univ _⟩)
      simp
    · simp
  have hh := congrArg norm hder
  rw [norm_prod] at hh
  rw [← hh]
  simp [Polynomial.derivative_pow, Polynomial.derivative_sub, Polynomial.derivative_X,
    Polynomial.derivative_one, norm_pow, hζ.norm'_eq_one hs.ne']

private lemma roots_vandermonde_lower {s : ℕ} (hs : 0 < s) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ s) : 1 ≤ vandermonde (fun i : Fin s => ζ ^ i.val) := by
  classical
  have h := Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag
    (fun i j : Fin s => ‖ζ^i.val - ζ^j.val‖)
  have hsq : vandermonde (fun i : Fin s => ζ^i.val)^2 = (s:ℝ)^s := by
    calc
      _ = ∏ i : Fin s, ∏ j ∈ Finset.Ioi i,
          (‖ζ^j.val-ζ^i.val‖ * ‖ζ^i.val-ζ^j.val‖) := by
        simp only [vandermonde, sq, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i hi
        apply Finset.prod_congr rfl
        intro j hj
        rw [norm_sub_rev (ζ^j.val) (ζ^i.val)]
      _ = ∏ i : Fin s, ∏ j ∈ {i}ᶜ, ‖ζ^j.val-ζ^i.val‖ := h
      _ = ∏ i : Fin s, (s:ℝ) := by
        apply Finset.prod_congr rfl
        intro i hi
        simpa only [Finset.compl_singleton, norm_sub_rev] using root_row_product hs hζ i
      _ = _ := by simp
  have hpow : 1 ≤ (s:ℝ)^s := one_le_pow₀ (by exact_mod_cast hs)
  have hnonneg : 0 ≤ vandermonde (fun i : Fin s => ζ^i.val) :=
    Finset.prod_nonneg (fun i hi => Finset.prod_nonneg (fun j hj => norm_nonneg _))
  nlinarith
private lemma tuple_norm (a : ℂ) (ha : a ∈ K) : ‖a‖ ≤ 4 := by
  rcases ha with ha | ha
  · have h : ‖a‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using ha
    linarith
  · simp only [Set.mem_singleton_iff] at ha
    subst a
    norm_num

private lemma tuple_disc (a : ℂ) (ha : a ∈ K) (h : a ≠ 4) : ‖a‖ ≤ 1 := by
  rcases ha with ha | ha
  · simpa [Metric.mem_closedBall, dist_eq_norm] using ha
  · exact False.elim (h (Set.mem_singleton_iff.mp ha))

private lemma tuple_vandermonde_upper {s : ℕ} (a : Fin s → ℂ) (ha : ∀ i, a i ∈ K) :
    vandermonde a ≤ ((4:ℝ)*s)^s := by
  classical
  rw [← norm_det_vandermonde]
  by_cases hinj : Function.Injective a
  · have ht : ∀ σ : Equiv.Perm (Fin s),
        ∏ i : Fin s, ‖(Matrix.vandermonde a) (σ i) i‖ ≤ (4:ℝ)^s := by
      intro σ
      simp only [Matrix.vandermonde_apply, norm_pow]
      by_cases he : ∃ j, a j = 4
      · obtain ⟨j, hj⟩ := he
        let i := σ.symm j
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        have hi : ‖a (σ i)‖ ^ i.val ≤ (4:ℝ)^s := by
          calc
            _ ≤ 4 ^ i.val := pow_le_pow_left₀ (norm_nonneg _) (tuple_norm _ (ha _)) _
            _ ≤ 4 ^ s := pow_le_pow_right₀ (by norm_num) i.isLt.le
        have hr : (∏ b ∈ Finset.univ.erase i, ‖a (σ b)‖^b.val) ≤ 1 := by
          apply Finset.prod_le_one₀ (fun b hb => by positivity)
          intro b hb
          apply pow_le_one₀ (norm_nonneg _)
          apply tuple_disc _ (ha _)
          intro heq
          have : σ b = j := hinj (heq.trans hj.symm)
          have : b = i := by simpa [i] using congrArg σ.symm this
          exact (Finset.mem_erase.mp hb).1 this
        exact (mul_le_mul hi hr (Finset.prod_nonneg fun b hb => by positivity)
          (by positivity)).trans_eq (mul_one _)
      · have hprod : (∏ i : Fin s, ‖a (σ i)‖^i.val) ≤ 1 := by
          apply Finset.prod_le_one₀ (fun b hb => by positivity)
          intro i hi
          apply pow_le_one₀ (norm_nonneg _)
          exact tuple_disc _ (ha _) (fun h => he ⟨_, h⟩)
        exact hprod.trans (one_le_pow₀ (by norm_num))
    calc
      _ ≤ ∑ σ : Equiv.Perm (Fin s), ‖Equiv.Perm.sign σ •
          ∏ i : Fin s, (Matrix.vandermonde a) (σ i) i‖ := by
        rw [Matrix.det_apply]
        exact norm_sum_le _ _
      _ = ∑ σ : Equiv.Perm (Fin s), ∏ i : Fin s,
          ‖(Matrix.vandermonde a) (σ i) i‖ := by
        apply Finset.sum_congr rfl
        intro σ hσ
        rcases Int.units_eq_one_or σ.sign with h | h <;> simp [h, norm_prod]
      _ ≤ ∑ _σ : Equiv.Perm (Fin s), (4:ℝ)^s :=
        Finset.sum_le_sum (fun σ hσ => ht σ)
      _ = (s.factorial:ℝ) * 4^s := by simp [Fintype.card_perm]
      _ ≤ (s:ℝ)^s * 4^s := by
        gcongr
        exact_mod_cast Nat.factorial_le_pow s
      _ = _ := by rw [← mul_pow]; congr 1; ring
  · have hz : (Matrix.vandermonde a).det = 0 := by
      by_contra hn
      exact hinj (Matrix.det_vandermonde_ne_zero_iff.mp hn)
    rw [hz, norm_zero]
    positivity

private lemma tuple_sup_bdd (s : ℕ) :
    BddAbove (Set.range (fun a : {a : Fin s → ℂ // ∀ i, a i ∈ K} => vandermonde a.1)) := by
  refine ⟨((4:ℝ)*s)^s, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact tuple_vandermonde_upper a.1 a.2

private lemma pointDiameter_bounds (s : ℕ) (hs : 2 ≤ s) :
    1 ≤ pointDiameter K s ∧ pointDiameter K s ≤
      Real.exp (2 * (Real.log 4 + Real.log s) / ((s:ℝ)-1)) := by
  classical
  have hs0 : 0 < s := by omega
  have hsR : 2 ≤ (s:ℝ) := by exact_mod_cast hs
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / s)
  have hζ : IsPrimitiveRoot ζ s := Complex.isPrimitiveRoot_exp s hs0.ne'
  let a : {a : Fin s → ℂ // ∀ i, a i ∈ K} := ⟨fun i => ζ^i.val, by
    intro i
    apply Or.inl
    simp only [Metric.mem_closedBall, dist_zero_right, norm_pow, hζ.norm'_eq_one hs0.ne', one_pow, le_refl]⟩
  have hlow : 1 ≤ ⨆ a : {a : Fin s → ℂ // ∀ i, a i ∈ K}, vandermonde a.1 :=
    (roots_vandermonde_lower hs0 hζ).trans (le_ciSup (tuple_sup_bdd s) a)
  have hexp : 0 ≤ (2:ℝ) / (s * (s-1):ℝ) :=
    div_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (by linarith))
  constructor
  · exact Real.one_le_rpow hlow hexp
  · have hupper : (⨆ a : {a : Fin s → ℂ // ∀ i, a i ∈ K}, vandermonde a.1) ≤
        ((4:ℝ)*s)^s := by
      have : Nonempty {a : Fin s → ℂ // ∀ i, a i ∈ K} := ⟨a⟩
      exact ciSup_le (fun a => tuple_vandermonde_upper a.1 a.2)
    unfold pointDiameter
    calc
      _ ≤ (((4:ℝ)*s)^s) ^ ((2:ℝ)/(s*(s-1):ℝ)) :=
        Real.rpow_le_rpow (by linarith) hupper hexp
      _ = Real.exp (2 * (Real.log 4 + Real.log s) / ((s:ℝ)-1)) := by
        rw [← Real.rpow_natCast_mul (by positivity), Real.rpow_def_of_pos (by positivity),
          Real.log_mul (by norm_num) (by positivity)]
        congr 1
        field_simp

private theorem diameter_one : TransfiniteDiameterOne K := by
  have hlog : Tendsto (fun s : ℕ => Real.log (s:ℝ) / ((s:ℝ)-1)) atTop (nhds 0) := by
    simpa [sub_eq_add_neg, Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun s : ℕ => (s:ℝ)-1) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1:ℝ)
      (tendsto_natCast_atTop_atTop : Tendsto (fun s : ℕ => (s:ℝ)) atTop atTop)
  have hc : Tendsto (fun s : ℕ => Real.log 4 / ((s:ℝ)-1)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have he : Tendsto (fun s : ℕ => Real.exp (2*(Real.log 4 + Real.log s)/((s:ℝ)-1)))
      atTop (nhds 1) := by
    have h : Tendsto (fun s : ℕ => 2 * (Real.log 4 / ((s:ℝ)-1) + Real.log s / ((s:ℝ)-1)))
        atTop (nhds 0) := by simpa using (hc.add hlog).const_mul 2
    have ht := Real.continuous_exp.tendsto 0 |>.comp h
    convert ht using 1
    · ext s
      simp only [Function.comp_apply]
      congr 1
      ring
    · simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
  · filter_upwards [eventually_ge_atTop 2] with s hs using (pointDiameter_bounds s hs).1
  · filter_upwards [eventually_ge_atTop 2] with s hs using (pointDiameter_bounds s hs).2


private def competitor (N k : ℕ) : Polynomial ℂ :=
  (Polynomial.X ^ N - 1) * (Polynomial.X - Polynomial.C 4)^k

private lemma competitor_mem (N k : ℕ) (hN : 0 < N) :
    InP (Metric.closedBall 0 1 ∪ {4}) (N+k) (competitor N k) := by
  have hmono : (Polynomial.X ^ N - (1 : Polynomial ℂ)).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : ℂ) (Nat.ne_of_gt hN)
  refine ⟨hmono.mul ((Polynomial.monic_X_sub_C (4 : ℂ)).pow k), ?_, ?_⟩
  · change (((Polynomial.X ^ N - Polynomial.C (1:ℂ)) * (Polynomial.X - Polynomial.C 4)^k).natDegree) = N+k
    rw [Polynomial.natDegree_mul (by simpa using hmono.ne_zero) (((Polynomial.monic_X_sub_C (4 : ℂ)).pow k).ne_zero)]
    simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
    congr 1
    exact (Polynomial.C_1 (R := ℂ)) ▸ (Polynomial.natDegree_X_pow_sub_C (n := N) (r := (1:ℂ)))
  · intro z hz
    have he : (z^N-1)*(z-4)^k=0 := by simpa [competitor, Polynomial.IsRoot.def] using hz
    rcases mul_eq_zero.mp he with h | h
    · have hp : ‖z‖^N=1 := by
        have heq : z^N=1 := sub_eq_zero.mp h
        simpa [norm_pow] using congrArg norm heq
      have hn : ‖z‖=1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.ne_of_gt hN)).mp hp
      exact Or.inl (by simp [Metric.mem_closedBall, dist_eq_norm, hn])
    · have hzk : z-4=0 := eq_zero_of_pow_eq_zero h
      exact Or.inr (by simp [sub_eq_zero.mp hzk])

private lemma competitor_cover (N k : ℕ) (hk : 2 ≤ k) (hN : k*(k-2)+1 ≤ N) :
    {z : ℂ | ‖(competitor N k).eval z‖ < 1} ⊆
      (Metric.ball 0 (1+(1/2:ℝ)^k) \ Metric.closedBall 0 (1-(1/2:ℝ)^k)) ∪
      Metric.ball 4 ((1/2:ℝ)^(k-2)) := by
  have hNp : 0 < N := by omega
  have hkp : 0 < k := by omega
  intro z hz
  have hp : ‖z^N-1‖ * ‖z-4‖^k < 1 := by
    simpa [competitor, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
      norm_mul, norm_pow] using hz
  by_cases hd : 2 ≤ ‖z-4‖
  · left
    have htwo : (0:ℝ)<2^k := by positivity
    have hpow : (2:ℝ)^k ≤ ‖z-4‖^k := pow_le_pow_left₀ (by norm_num) hd _
    have he : ‖z^N-1‖ < (1/2:ℝ)^k := by
      have hm : ‖z^N-1‖ * (2:ℝ)^k < 1 :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)) hp
      have heq : (1/2:ℝ)^k * 2^k = 1 := by rw [← mul_pow]; norm_num
      nlinarith
    have hab : |‖z‖^N-1| ≤ ‖z^N-1‖ := by
      simpa [norm_pow] using abs_norm_sub_norm_le (z^N) (1:ℂ)
    have hu : ‖z‖^N < 1+(1/2:ℝ)^k := by
      have := (abs_lt.mp (lt_of_le_of_lt hab he)).2
      linarith
    have hl : 1-(1/2:ℝ)^k < ‖z‖^N := by
      have := (abs_lt.mp (lt_of_le_of_lt hab he)).1
      linarith
    have hzup : ‖z‖ < 1+(1/2:ℝ)^k := by
      by_cases hz1 : 1 ≤ ‖z‖
      · exact lt_of_le_of_lt (le_self_pow₀ hz1 (Nat.ne_of_gt hNp)) hu
      · have hdpos : 0 < (1/2:ℝ)^k := by positivity
        linarith
    have hzlo : 1-(1/2:ℝ)^k < ‖z‖ := by
      by_cases hz1 : ‖z‖ ≤ 1
      · have hs : ‖z‖^N ≤ ‖z‖ := pow_le_of_le_one (norm_nonneg _) hz1 (Nat.ne_of_gt hNp)
        exact lt_of_lt_of_le hl hs
      · have hdpos : 0 < (1/2:ℝ)^k := by positivity
        linarith
    simpa [Metric.mem_ball, Metric.mem_closedBall, dist_eq_norm] using And.intro hzup (not_le.mpr hzlo)
  · right
    have hd' : ‖z-4‖ < 2 := lt_of_not_ge hd
    have hz2 : 2 < ‖z‖ := by
      have ht := norm_sub_le_norm_sub_add_norm_sub (4:ℂ) z 0
      norm_num [norm_sub_rev] at ht
      linarith
    have hzn : (2:ℝ)^N ≤ ‖z‖^N := pow_le_pow_left₀ (by norm_num) hz2.le _
    have htri : ‖z‖^N-1 ≤ ‖z^N-1‖ := by
      simpa [norm_pow] using norm_sub_norm_le (z^N) (1:ℂ)
    have hNp' : N = (N-1)+1 := by omega
    have ht : 1 ≤ (2:ℝ)^(N-1) := one_le_pow₀ (by norm_num)
    have hl : (2:ℝ)^(N-1) ≤ ‖z^N-1‖ := by
      have hzn' : (2:ℝ)^(N-1)*2 ≤ ‖z‖^N := by
        calc
          _ = (2:ℝ)^N := by rw [← pow_succ, ← hNp']
          _ ≤ _ := hzn
      nlinarith only [hzn', htri, ht]
    have hexp : k*(k-2) ≤ N-1 := by omega
    have hlarge : (2:ℝ)^(k*(k-2)) ≤ (2:ℝ)^(N-1) :=
      pow_le_pow_right₀ (by norm_num) hexp
    have hr : ((1/2:ℝ)^(k-2))^k * (2:ℝ)^(k*(k-2)) = 1 := by
      rw [← pow_mul, Nat.mul_comm (k-2) k, ← mul_pow]
      norm_num
    have hsmall : ‖z-4‖ < (1/2:ℝ)^(k-2) := by
      by_contra h
      have hdist : ((1/2:ℝ)^(k-2))^k ≤ ‖z-4‖^k :=
        pow_le_pow_left₀ (by positivity) (le_of_not_gt h) _
      have hbad : 1 ≤ ‖z^N-1‖*‖z-4‖^k := by
        calc
          1 = ((1/2:ℝ)^(k-2))^k * (2:ℝ)^(k*(k-2)) := hr.symm
          _ ≤ ‖z-4‖^k * ‖z^N-1‖ := mul_le_mul hdist (hlarge.trans hl) (by positivity) (by positivity)
          _ = _ := mul_comm _ _
      linarith
    simpa [Metric.mem_ball, dist_eq_norm] using hsmall
private lemma area_upper (N k : ℕ) (hk : 2 ≤ k) (hN : k*(k-2)+1 ≤ N) :
    lemniscateArea (competitor N k) ≤ ENNReal.ofReal (20*Real.pi*(1/2:ℝ)^k) := by
  let δ : ℝ := (1/2:ℝ)^k
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hd1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hinner : 0 ≤ 1-δ := by linarith
  have houter : 0 ≤ 1+δ := by positivity
  have hr : (1/2:ℝ)^(k-2)=4*δ := by
    have hk' : k=(k-2)+2 := by omega
    dsimp [δ]
    conv_rhs => rw [hk', pow_add]
    norm_num
    ring
  have hball (a : ℂ) (r : ℝ) (hr : 0 ≤ r) :
      volume (Metric.ball a r) = ENNReal.ofReal (Real.pi*r^2) := by
    rw [Complex.volume_ball]
    rw [ENNReal.ofReal_mul Real.pi_nonneg, ENNReal.ofReal_pow hr]
    simp [mul_comm, ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  have hclosed (a : ℂ) (r : ℝ) (hr : 0 ≤ r) :
      volume (Metric.closedBall a r) = ENNReal.ofReal (Real.pi*r^2) := by
    rw [Complex.volume_closedBall]
    rw [ENNReal.ofReal_mul Real.pi_nonneg, ENNReal.ofReal_pow hr]
    simp [mul_comm, ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  have hsub : Metric.closedBall (0:ℂ) (1-δ) ⊆ Metric.ball 0 (1+δ) := by
    intro z hz
    simp only [Metric.mem_closedBall, Metric.mem_ball] at *
    linarith
  have hann : volume (Metric.ball (0:ℂ) (1+δ) \ Metric.closedBall 0 (1-δ)) =
      ENNReal.ofReal (4*Real.pi*δ) := by
    rw [measure_sdiff hsub Metric.isClosed_closedBall.measurableSet.nullMeasurableSet
      (by rw [hclosed _ _ hinner]; exact ENNReal.ofReal_ne_top)]
    rw [hball _ _ houter, hclosed _ _ hinner, ← ENNReal.ofReal_sub _ (by positivity : 0 ≤ Real.pi*(1-δ)^2)]
    congr 1
    ring
  have hrad : Real.pi*((1/2:ℝ)^(k-2))^2 ≤ 16*Real.pi*δ := by
    rw [hr]
    have hd2 : δ^2 ≤ δ := by nlinarith
    nlinarith [Real.pi_nonneg]
  calc
    lemniscateArea (competitor N k) ≤
        volume ((Metric.ball (0:ℂ) (1+δ) \ Metric.closedBall 0 (1-δ)) ∪
          Metric.ball 4 ((1/2:ℝ)^(k-2))) := measure_mono (competitor_cover N k hk hN)
    _ ≤ volume (Metric.ball (0:ℂ) (1+δ) \ Metric.closedBall 0 (1-δ)) +
        volume (Metric.ball (4:ℂ) ((1/2:ℝ)^(k-2))) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (4*Real.pi*δ) + ENNReal.ofReal (16*Real.pi*δ) := by
      rw [hann, hball _ _ (by positivity)]
      exact add_le_add_right (ENNReal.ofReal_le_ofReal hrad) _
    _ = ENNReal.ofReal (20*Real.pi*δ) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

private lemma minimalArea_bound {K : Set ℂ} {n : ℕ} {p : Polynomial ℂ} {C : ℝ}
    (hp : InP K n p) (hC : 0 ≤ C) (hb : lemniscateArea p ≤ ENNReal.ofReal C) :
    (minimalArea K n).toReal ≤ C := by
  have hm : minimalArea K n ≤ ENNReal.ofReal C :=
    iInf_le_of_le p (iInf_le_of_le hp hb)
  have hfinite : minimalArea K n ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm
  have hreal := (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).mpr hm
  simpa only [ENNReal.toReal_ofReal hC] using hreal

private def degreeSeq (k : ℕ) := k ^ 2 + k + 1
private lemma degreeSeq_tendsto : Tendsto degreeSeq atTop atTop := by
  apply tendsto_atTop_mono (fun k => show k ≤ degreeSeq k by dsimp [degreeSeq]; omega)
  exact tendsto_id
private lemma geometric_decay (C : ℝ) :
    Tendsto (fun k : ℕ => (degreeSeq k : ℝ) * (C * (1 / 2 : ℝ)^k)) atTop (nhds 0) := by
  have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 2
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  convert ((h2.add h1).add h0).mul_const C using 1
  · ext k
    simp only [degreeSeq, Nat.cast_add, Nat.cast_pow, Nat.cast_one, pow_one]
    ring
  · simp
private lemma reciprocal_nat_bigO_log :
    (fun n : ℕ => 1 / (n : ℝ)) =O[atTop] (fun n : ℕ => 1 / Real.log n) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hp := Real.log_pos hn'
  have hl : Real.log (n : ℝ) ≤ n := by linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < n)]
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (n : ℝ)),
    abs_of_nonneg (by positivity : 0 ≤ 1 / Real.log (n : ℝ)), one_mul]
  exact one_div_le_one_div_of_le hp hl
private lemma no_reciprocal_bigO (A : ℕ → ℝ) (hA : ∀ n, 0 ≤ A n) (C : ℝ)
    (hbound : ∀ᶠ k in atTop, A (degreeSeq k) ≤ C * (1 / 2 : ℝ)^k) :
    ¬ (fun n : ℕ => 1 / (n : ℝ)) =O[atTop] A := by
  intro h
  obtain ⟨c, hc, hcA⟩ := h.exists_pos
  have hsmall := (geometric_decay (c*C)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hall := (degreeSeq_tendsto.eventually hcA.bound).and (hbound.and hsmall)
  obtain ⟨k, hk⟩ := hall.exists
  have hd : (0 : ℝ) < degreeSeq k := by
    have : 0 < degreeSeq k := by dsimp [degreeSeq]; omega
    exact_mod_cast this
  have hb : 1 / (degreeSeq k : ℝ) ≤ c * A (degreeSeq k) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (degreeSeq k : ℝ)),
      abs_of_nonneg (hA _)] using hk.1
  have hm := mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hk.2.1 hc.le)) hd.le
  rw [mul_one_div_cancel hd.ne'] at hm
  have he : (degreeSeq k : ℝ) * (c * (C * (1 / 2 : ℝ)^k)) =
      (degreeSeq k : ℝ) * ((c*C) * (1 / 2 : ℝ)^k) := by ring
  rw [he] at hm
  exact (not_le_of_gt hk.2.2) hm

private lemma subsequence_area_bound (k : ℕ) (hk : 2 ≤ k) :
    (minimalArea K (degreeSeq k)).toReal ≤ (20 * Real.pi) * (1/2:ℝ)^k := by
  have hN : k*(k-2)+1 ≤ k^2+1 := by
    have hm := Nat.mul_le_mul_left k (Nat.sub_le k 2)
    simpa only [pow_two] using Nat.add_le_add_right hm 1
  have hp : InP K (degreeSeq k) (competitor (k^2+1) k) := by
    have h := competitor_mem (k^2+1) k (by omega)
    convert h using 1 <;> simp [K, degreeSeq, Nat.add_right_comm]
  exact minimalArea_bound hp (by positivity) (area_upper (k^2+1) k hk hN)

theorem result : ¬ claim := by
  intro h
  have hcompact : IsCompact K := (isCompact_closedBall (0 : ℂ) 1).union isCompact_singleton
  have hnonempty : K.Nonempty := ⟨0, Or.inl (by simp)⟩
  have hclaimed := h K hcompact hnonempty diameter_one
  have hb : ∀ᶠ k in atTop,
      (minimalArea K (degreeSeq k)).toReal ≤ (20*Real.pi)*(1/2:ℝ)^k := by
    filter_upwards [eventually_ge_atTop 2] with k hk using subsequence_area_bound k hk
  have hnot := no_reciprocal_bigO (fun n => (minimalArea K n).toReal)
    (fun _ => ENNReal.toReal_nonneg) (20*Real.pi) hb
  rcases hclaimed with hrate | hrate
  · exact hnot hrate.isBigO_symm
  · exact hnot (reciprocal_nat_bigO_log.trans hrate.isBigO_symm)

end D5.S3.Analytic.Lemniscates.CapacityOneAreaDecayRate
