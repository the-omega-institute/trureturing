/- GID: D5/S3/Quantum/Analysis/OrliczCommonEnergy
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/OrliczCommonEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The genuine logarithmic Orlicz conjugate and its consumed common-energy tail route. -/

/- These are infinite-family analytic existence and inequality statements. They
   do not certify a finite instance, enumerate a bounded domain, provide a
   decision procedure or reduce a numerical computation. -/

import D5.S3.Analytic.SeriesInequalities.UniformTailAmplification
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

noncomputable section
open Filter Set Topology
open scoped BigOperators ENNReal NNReal Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Analysis.OrliczCommonEnergy

/-! The scalar functions are kept as the actual logarithmic formula. -/

def phi (p t : ℝ) : ℝ := t * (Real.log (max 1 t)) ^ p

def conjugate (p u : ℝ) : ℝ :=
  sSup ((fun t : Set.Ici (0 : ℝ) => u * (t : ℝ) - phi p t) '' Set.univ)

private lemma phi_nonneg {p : ℝ} (_hp : 0 ≤ p) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ phi p t := by
  unfold phi
  exact mul_nonneg ht (Real.rpow_nonneg (Real.log_nonneg (le_max_left _ _)) p)

private lemma phi_zero {p : ℝ} : phi p 0 = 0 := by
  simp [phi]

private lemma conjugate_pointwise_le {p u : ℝ} (hp : 0 < p) (hu : 0 ≤ u)
    {t : Set.Ici (0 : ℝ)} :
    u * (t : ℝ) - phi p (t : ℝ) ≤ u * Real.exp (u ^ p⁻¹) := by
  have ht : 0 ≤ (t : ℝ) := t.2
  by_cases ht1 : (t : ℝ) ≤ 1
  · have hlog : Real.log (max 1 (t : ℝ)) = 0 := by
      rw [max_eq_left ht1, Real.log_one]
    rw [phi, hlog, Real.zero_rpow hp.ne', mul_zero, sub_zero]
    calc
      u * (t : ℝ) ≤ u * 1 := mul_le_mul_of_nonneg_left ht1 hu
      _ ≤ u * Real.exp (u ^ p⁻¹) := by
        have huPow : 0 ≤ u ^ p⁻¹ := Real.rpow_nonneg hu _
        exact mul_le_mul_of_nonneg_left (Real.one_le_exp huPow) hu
  · have ht1' : 1 < (t : ℝ) := lt_of_not_ge ht1
    have hlog : 0 < Real.log (t : ℝ) := Real.log_pos ht1'
    have hmax : max 1 (t : ℝ) = (t : ℝ) := max_eq_right ht1'.le
    by_cases hpow : u ≤ (Real.log (t : ℝ)) ^ p
    · have hphi : 0 ≤ phi p (t : ℝ) := by
        rw [phi, hmax]
        exact mul_nonneg ht (Real.rpow_nonneg hlog.le p)
      have hle : u * (t : ℝ) ≤ phi p (t : ℝ) := by
        rw [phi, hmax]
        simpa [mul_comm] using (mul_le_mul_of_nonneg_left hpow ht)
      exact (sub_nonpos.mpr hle).trans (by positivity)
    · have hpow' : (Real.log (t : ℝ)) ^ p < u := lt_of_not_ge hpow
      have hlog_le : Real.log (t : ℝ) ≤ u ^ p⁻¹ :=
        (Real.le_rpow_inv_iff_of_pos hlog.le hu hp).2 hpow'.le
      have ht_exp : (t : ℝ) ≤ Real.exp (u ^ p⁻¹) :=
        (Real.log_le_iff_le_exp (by positivity)).1 hlog_le
      have hphi : 0 ≤ phi p (t : ℝ) := by
        rw [phi, hmax]
        exact mul_nonneg ht (Real.rpow_nonneg hlog.le p)
      calc
        u * (t : ℝ) - phi p (t : ℝ) ≤ u * (t : ℝ) := sub_le_self _ hphi
        _ ≤ u * Real.exp (u ^ p⁻¹) := mul_le_mul_of_nonneg_left ht_exp hu

theorem conjugate_nonempty_bddAbove {p u : ℝ} (hp : 0 < p) (hu : 0 ≤ u) :
    ((fun t : Set.Ici (0 : ℝ) => u * (t : ℝ) - phi p t) '' Set.univ).Nonempty ∧
      BddAbove ((fun t : Set.Ici (0 : ℝ) => u * (t : ℝ) - phi p t) '' Set.univ) := by
  constructor
  · refine ⟨0, ?_⟩
    refine ⟨⟨0, by simp⟩, Set.mem_univ _, ?_⟩
    simp [phi_zero]
  · refine ⟨u * Real.exp (u ^ p⁻¹), ?_⟩
    rintro _ ⟨t, -, rfl⟩
    exact conjugate_pointwise_le hp hu

theorem conjugate_nonneg {p u : ℝ} (hp : 0 < p) (hu : 0 ≤ u) :
    0 ≤ conjugate p u := by
  obtain ⟨hne, hbd⟩ := conjugate_nonempty_bddAbove hp hu
  apply le_csSup hbd
  exact ⟨⟨0, by simp⟩, Set.mem_univ _, by simp [phi_zero]⟩

theorem conjugate_le_majorant {p u : ℝ} (hp : 0 < p) (hu : 0 ≤ u) :
    conjugate p u ≤ u * Real.exp (u ^ p⁻¹) := by
  obtain ⟨hne, hbd⟩ := conjugate_nonempty_bddAbove hp hu
  apply csSup_le hne
  rintro _ ⟨t, -, rfl⟩
  exact conjugate_pointwise_le hp hu

theorem fenchel_young {p u t : ℝ} (hp : 0 < p) (hu : 0 ≤ u) (ht : 0 ≤ t) :
    u * t ≤ phi p t + conjugate p u := by
  have hbd := (conjugate_nonempty_bddAbove hp hu).2
  have hmem : u * t - phi p t ∈
      ((fun z : Set.Ici (0 : ℝ) => u * (z : ℝ) - phi p (z : ℝ)) '' Set.univ) := by
    exact ⟨⟨t, ht⟩, Set.mem_univ _, rfl⟩
  have hs := le_csSup hbd hmem
  have hs' : u * t - phi p t ≤ conjugate p u := by
    simpa [conjugate] using hs
  simpa [add_comm] using (sub_le_iff_le_add.mp hs')

/-! An ENNReal tail lemma records the actual every-scale Young argument.  The
assumption `hpoint` is a pointwise Fenchel estimate; no tail field is passed
to the theorem. -/

theorem uniform_tail_from_young
    {X : Type*} (f : X → ℕ → ℝ≥0∞) (A : X → ℕ → ℝ≥0∞)
    (B : ℝ≥0 → ℕ → ℝ≥0∞) (M : ℝ≥0∞)
    (hM : ∀ x, (∑' n, A x n) ≤ M) (hMtop : M ≠ ∞)
    (hpoint : ∀ (a : ℝ≥0), 0 < a → ∀ x n,
      (a : ℝ≥0∞) * f x n ≤ A x n + B a n)
    (hdual : ∀ a : ℝ≥0, 0 < a → (∑' n, B a n) ≠ ∞) :
    ∀ ε : ℝ≥0, 0 < ε →
      ∃ N : ℕ, ∀ x, (∑' k, f x (N + k)) ≤ (ε : ℝ≥0∞) := by
  intro ε hε
  have hhalf : ((ε : ℝ≥0∞) / 2) ≠ 0 := by
    exact (ENNReal.div_pos (ENNReal.coe_pos.mpr hε).ne' (by norm_num)).ne'
  obtain ⟨r, hrpos, hrM⟩ := ENNReal.exists_nnreal_pos_mul_lt hMtop hhalf
  let a : ℝ≥0 := r⁻¹
  have hapos : 0 < a := by
    dsimp [a]
    exact inv_pos.mpr hrpos
  have har : (r : ℝ≥0∞) * (a : ℝ≥0∞) = 1 := by
    dsimp [a]
    rw [ENNReal.coe_inv hrpos.ne']
    exact ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr hrpos.ne') ENNReal.coe_ne_top
  let q : ℝ≥0∞ := (ε : ℝ≥0∞) / 2 / (r : ℝ≥0∞)
  have hqpos : 0 < q := by
    dsimp [q]
    exact ENNReal.div_pos hhalf ENNReal.coe_ne_top
  have hq : q ≠ 0 := hqpos.ne'
  have hdual_lim : Tendsto (fun N : ℕ => ∑' k, B a (N + k)) atTop (𝓝 0) :=
    by simpa [Nat.add_comm] using ENNReal.tendsto_sum_nat_add (B a) (hdual a hapos)
  obtain ⟨N, hN⟩ := (tendsto_order.1 hdual_lim).2 q hqpos |>.exists
  refine ⟨N, fun x => ?_⟩
  have hAtail : (∑' k, A x (N + k)) ≤ M := by
    calc
      (∑' k, A x (N + k)) ≤ ∑' n, A x n := by
        exact ENNReal.tsum_comp_le_tsum_of_injective
          (fun _ _ h => Nat.add_left_cancel h) (A x)
      _ ≤ M := hM x
  have hpoint' : ∀ k, f x (N + k) ≤
      (r : ℝ≥0∞) * (A x (N + k) + B a (N + k)) := by
    intro k
    have hk := hpoint a hapos x (N + k)
    calc
      f x (N + k) = (r : ℝ≥0∞) * ((a : ℝ≥0∞) * f x (N + k)) := by
        rw [← mul_assoc, har, one_mul]
      _ ≤ (r : ℝ≥0∞) * (A x (N + k) + B a (N + k)) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
  calc
    (∑' k, f x (N + k)) ≤
        ∑' k, (r : ℝ≥0∞) * (A x (N + k) + B a (N + k)) :=
      ENNReal.tsum_le_tsum hpoint'
    _ = (r : ℝ≥0∞) * ((∑' k, A x (N + k)) + ∑' k, B a (N + k)) := by
      rw [ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    _ ≤ (r : ℝ≥0∞) * (M + q) := by
      gcongr
    _ ≤ (ε : ℝ≥0∞) := by
      have hq' : (r : ℝ≥0∞) * q = (ε : ℝ≥0∞) / 2 := by
        dsimp [q]
        rw [ENNReal.mul_div_cancel (ENNReal.coe_ne_zero.mpr hrpos.ne') ENNReal.coe_ne_top]
      rw [mul_add, hq', add_comm]
      calc
        (ε : ℝ≥0∞) / 2 + (r : ℝ≥0∞) * M ≤
            (ε : ℝ≥0∞) / 2 + (ε : ℝ≥0∞) / 2 := add_le_add le_rfl hrM.le
        _ = (ε : ℝ≥0∞) := ENNReal.add_halves _

def baseTerm (p : ℝ) (s : ℕ → ℝ) (d : ℕ → ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (s n * phi p (d n / s n))

def dualTerm (p : ℝ) (s h : ℕ → ℝ) (a : ℝ≥0) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (s n * conjugate p ((a : ℝ) * h n))

def energyTerm (h : ℕ → ℝ) (d : ℕ → ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (h n * d n)

def amplifiedEnergy (w : ℕ → ℕ) (h : ℕ → ℝ) (d : ℕ → ℝ) (n : ℕ) : ℝ≥0∞ :=
  (w n : ℝ≥0∞) * energyTerm h d n

theorem orlicz_uniform_energy_tail
    {X : Type*} {p : ℝ} (hp : 0 < p)
    (s h : ℕ → ℝ) (d : X → ℕ → ℝ)
    (hs : ∀ n, 0 < s n) (hh : ∀ n, 0 ≤ h n)
    (hd : ∀ x n, 0 ≤ d x n) (M : ℝ≥0∞)
    (hM : ∀ x, (∑' n, baseTerm p s (d x) n) ≤ M) (hMtop : M ≠ ∞)
    (hdual : ∀ a : ℝ≥0, 0 < a →
      (∑' n, dualTerm p s h a n) ≠ ∞) :
    ∀ ε : ℝ≥0, 0 < ε →
      ∃ N : ℕ, ∀ x, (∑' k, energyTerm h (d x) (N + k)) ≤ (ε : ℝ≥0∞) := by
  intro ε hε
  apply uniform_tail_from_young
    (f := fun x n => energyTerm h (d x) n)
    (A := fun x n => baseTerm p s (d x) n)
    (B := fun a n => dualTerm p s h a n) M hM hMtop ?_ hdual ε hε
  intro a ha x n
  have hsn : 0 < s n := hs n
  have hdn : 0 ≤ d x n := hd x n
  have hun : 0 ≤ (a : ℝ) * h n :=
    mul_nonneg (NNReal.coe_nonneg a) (hh n)
  have hfen := fenchel_young hp hun (div_nonneg hdn hsn.le)
  have hmul := mul_le_mul_of_nonneg_left hfen hsn.le
  have hreal : (a : ℝ) * (h n * d x n) ≤
      s n * phi p (d x n / s n) + s n * conjugate p ((a : ℝ) * h n) := by
    calc
      (a : ℝ) * (h n * d x n) = s n * ((a : ℝ) * h n * (d x n / s n)) := by
        field_simp [ne_of_gt hsn]
      _ ≤ s n * (phi p (d x n / s n) + conjugate p ((a : ℝ) * h n)) := hmul
      _ = s n * phi p (d x n / s n) + s n * conjugate p ((a : ℝ) * h n) := by ring
  have hen := ENNReal.ofReal_le_ofReal hreal
  have hphi : 0 ≤ phi p (d x n / s n) :=
    phi_nonneg hp.le (div_nonneg hdn hsn.le)
  have hconj : 0 ≤ conjugate p ((a : ℝ) * h n) := conjugate_nonneg hp hun
  calc
    (a : ℝ≥0∞) * energyTerm h (d x) n =
        ENNReal.ofReal ((a : ℝ) * (h n * d x n)) := by
      rw [energyTerm, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (NNReal.coe_nonneg a)]
    _ ≤ ENNReal.ofReal (s n * phi p (d x n / s n) +
        s n * conjugate p ((a : ℝ) * h n)) := hen
    _ = baseTerm p s (d x) n + dualTerm p s h a n := by
      rw [ENNReal.ofReal_add (mul_nonneg hsn.le hphi) (mul_nonneg hsn.le hconj)]
      rfl

theorem exists_amplified_orlicz_energy
    {X : Type*} {p : ℝ} (hp : 0 < p)
    (s h : ℕ → ℝ) (d : X → ℕ → ℝ)
    (hs : ∀ n, 0 < s n) (hh : ∀ n, 0 ≤ h n)
    (hd : ∀ x n, 0 ≤ d x n) (M : ℝ≥0∞) (δ : ℝ≥0) (hδ : 0 < δ)
    (hM : ∀ x, (∑' n, baseTerm p s (d x) n) ≤ M) (hMtop : M ≠ ∞)
    (hdual : ∀ a : ℝ≥0, 0 < a →
      (∑' n, dualTerm p s h a n) ≠ ∞) :
    ∃ w : ℕ → ℕ,
      (∀ n, 1 ≤ w n) ∧ Monotone w ∧ Tendsto w atTop atTop ∧
      (∀ x, (∑' n, amplifiedEnergy w h (d x) n) ≤
        (∑' n, energyTerm h (d x) n) + (δ : ℝ≥0∞)) ∧
      (∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ, ∀ x,
        (∑' k, amplifiedEnergy w h (d x) (N + k)) ≤ (ε : ℝ≥0∞)) := by
  obtain ⟨w, hw1, hwmono, hwlim, hwcost, hwtail⟩ :=
    D5.S3.Analytic.SeriesInequalities.UniformTailAmplification.exists_uniform_tail_amplification
      (a := fun x n => energyTerm h (d x) n) δ hδ
      (orlicz_uniform_energy_tail hp s h d hs hh hd M hM hMtop hdual)
  refine ⟨w, hw1, hwmono, hwlim, ?_, ?_⟩
  · simpa [amplifiedEnergy] using hwcost
  · intro ε hε
    obtain ⟨N, hN⟩ := hwtail ε hε
    exact ⟨N, fun x => by simpa [amplifiedEnergy] using hN x⟩

/-- The logarithmic levels of a faithful reference distribution. -/
def logarithmicLevel (s : ℕ → ℝ) (n : ℕ) : ℝ := -Real.log (s n)

def commonLevel (w : ℕ → ℕ) (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  (w n : ℝ) * logarithmicLevel s n

def scalarEnergy (H : ℕ → ℝ) (d : ℕ → ℝ) : ℝ := ∑' n, H n * d n

lemma summable_of_uniform_ennreal_tails
    {X : Type*} (f : X → ℕ → ℝ) (hf : ∀ x n, 0 ≤ f x n)
    (hUT : ∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ, ∀ x,
      (∑' k, ENNReal.ofReal (f x (N + k))) ≤ (ε : ℝ≥0∞)) :
    ∀ x, Summable (f x) := by
  obtain ⟨N, hN⟩ := hUT 1 (by norm_num)
  intro x
  have hfinite : (∑' k, ENNReal.ofReal (f x (N + k))) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (hN x)
  have ht : Summable (fun k => f x (k + N)) := by
    simpa only [ENNReal.toReal_ofReal (hf x _), Nat.add_comm] using
      ENNReal.summable_toReal hfinite
  exact (summable_nat_add_iff N).1 ht

set_option maxHeartbeats 800000 in
-- Budget the uniform approximation and the two infinite-series coercion transfers.
lemma continuous_of_uniform_ennreal_tails
    {X : Type*} [TopologicalSpace X] (f : X → ℕ → ℝ)
    (hf : ∀ x n, 0 ≤ f x n) (hc : ∀ n, Continuous (fun x => f x n))
    (hUT : ∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ, ∀ x,
      (∑' k, ENNReal.ofReal (f x (N + k))) ≤ (ε : ℝ≥0∞)) :
    Continuous (fun x => ∑' n, f x n) := by
  have hsum := summable_of_uniform_ennreal_tails f hf hUT
  apply continuous_of_uniform_approx_of_continuous
  intro u hu
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
  let q : ℝ≥0 := ⟨ε / 2, by positivity⟩
  have hq : 0 < q := by exact_mod_cast (half_pos hε)
  obtain ⟨N, hN⟩ := hUT q hq
  refine ⟨fun x => ∑ n ∈ Finset.range N, f x n,
    continuous_finsetSum _ (fun n _ => hc n), fun x => ?_⟩
  apply hεu
  have htail : Summable (fun k => f x (N + k)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff N).2 (hsum x)
  have hbound : (∑' k, f x (N + k)) ≤ (q : ℝ) := by
    apply (ENNReal.ofReal_le_ofReal_iff q.coe_nonneg).mp
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => hf x _) htail]
    simpa only [ENNReal.ofReal_coe_nnreal] using hN x
  have hsplit := Summable.sum_add_tsum_nat_add (f := f x) N (hsum x)
  have hsplit' : (∑ n ∈ Finset.range N, f x n) +
      (∑' k, f x (N + k)) = ∑' n, f x n := by
    simpa only [Nat.add_comm] using hsplit
  change dist (∑' n, f x n) (∑ n ∈ Finset.range N, f x n) < ε
  rw [Real.dist_eq, ← hsplit', add_sub_cancel_left,
    abs_of_nonneg (tsum_nonneg (fun k => hf x _))]
  exact hbound.trans_lt (by change ε / 2 < ε; linarith)

private lemma reference_levels {s : ℕ → ℝ} (hs : ∀ n, 0 < s n)
    (hsum : HasSum s 1) :
    (∀ n, 0 ≤ logarithmicLevel s n) ∧
      Tendsto (logarithmicLevel s) atTop atTop := by
  constructor
  · intro n
    have hle : s n ≤ 1 := by
      simpa only [hsum.tsum_eq] using hsum.summable.le_tsum n (fun k _ => (hs k).le)
    exact neg_nonneg.mpr (Real.log_nonpos (hs n).le hle)
  · have hs0 : Tendsto s atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hsum.summable.tendsto_atTop_zero, Eventually.of_forall hs⟩
    exact tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hs0)

private lemma all_temperature_summable
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hsum : HasSum s 1)
    (w : ℕ → ℕ) (hwlim : Tendsto w atTop atTop)
    {β : ℝ} (hβ : 0 < β) :
    Summable (fun n => Real.exp (-β * commonLevel w s n)) := by
  have hh := (reference_levels hs hsum).1
  have hwR : Tendsto (fun n => (w n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwlim
  apply hsum.summable.of_norm_bounded_eventually_nat
  filter_upwards [hwR.eventually (eventually_ge_atTop β⁻¹)] with n hn
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  have hβw : 1 ≤ β * (w n : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hn hβ.le
    simpa only [mul_inv_cancel₀ hβ.ne'] using hm
  calc
    Real.exp (-β * commonLevel w s n) ≤ Real.exp (-logarithmicLevel s n) := by
      apply Real.exp_le_exp.mpr
      dsimp only [commonLevel]
      nlinarith [mul_le_mul_of_nonneg_right hβw (hh n)]
    _ = s n := by simp only [logarithmicLevel, neg_neg, Real.exp_log (hs n)]

/-- One common scalar energy for a coordinatewise continuous family of normalized
nonnegative masses. Finiteness is established before every real infinite sum is used.
The hypotheses are the actual extended Orlicz moment and every positive dual scale. -/
theorem exists_continuous_common_energy
    {X : Type*} [TopologicalSpace X] {p : ℝ} (hp : 0 < p)
    (s : ℕ → ℝ) (d : X → ℕ → ℝ)
    (hs : ∀ n, 0 < s n) (hsum : HasSum s 1)
    (hd : ∀ x n, 0 ≤ d x n) (_hdnorm : ∀ x, HasSum (d x) 1)
    (hdcont : ∀ n, Continuous (fun x => d x n))
    (M : ℝ≥0∞) (hM : ∀ x, (∑' n, baseTerm p s (d x) n) ≤ M)
    (hMtop : M ≠ ∞)
    (hdual : ∀ a : ℝ≥0, 0 < a →
      (∑' n, dualTerm p s (logarithmicLevel s) a n) ≠ ∞)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    ∃ w : ℕ → ℕ,
      (∀ n, 1 ≤ w n) ∧ Monotone w ∧ Tendsto w atTop atTop ∧
      (∀ n, logarithmicLevel s n ≤ commonLevel w s n) ∧
      Tendsto (commonLevel w s) atTop atTop ∧
      (∀ β : ℝ, 0 < β → Summable (fun n => Real.exp (-β * commonLevel w s n))) ∧
      (∀ x, Summable (fun n => logarithmicLevel s n * d x n)) ∧
      (∀ x, Summable (fun n => commonLevel w s n * d x n)) ∧
      Continuous (fun x => scalarEnergy (commonLevel w s) (d x)) ∧
      (∀ x, scalarEnergy (commonLevel w s) (d x) ≤
        scalarEnergy (logarithmicLevel s) (d x) + (δ : ℝ)) ∧
      (∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ, ∀ x,
        (∑' k, ENNReal.ofReal (commonLevel w s (N + k) * d x (N + k))) ≤
          (ε : ℝ≥0∞)) := by
  obtain ⟨hh, hhlim⟩ := reference_levels hs hsum
  have hbaseTail := orlicz_uniform_energy_tail hp s (logarithmicLevel s) d
    hs hh hd M hM hMtop hdual
  have hbase : ∀ x, Summable (fun n => logarithmicLevel s n * d x n) :=
    summable_of_uniform_ennreal_tails _ (fun x n => mul_nonneg (hh n) (hd x n)) hbaseTail
  obtain ⟨w, hw1, hwmono, hwlim, hwcost, hwtail⟩ :=
    exists_amplified_orlicz_energy hp s (logarithmicLevel s) d hs hh hd M δ hδ hM hMtop hdual
  have hHnonneg (n : ℕ) : 0 ≤ commonLevel w s n :=
    mul_nonneg (Nat.cast_nonneg _) (hh n)
  have hHlower (n : ℕ) : logarithmicLevel s n ≤ commonLevel w s n := by
    have hw : (1 : ℝ) ≤ w n := by exact_mod_cast hw1 n
    simpa only [one_mul, commonLevel] using mul_le_mul_of_nonneg_right hw (hh n)
  have hweightedTail : ∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ, ∀ x,
      (∑' k, ENNReal.ofReal (commonLevel w s (N + k) * d x (N + k))) ≤
        (ε : ℝ≥0∞) := by
    simpa only [commonLevel, amplifiedEnergy, energyTerm, mul_assoc,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using hwtail
  have hweighted : ∀ x, Summable (fun n => commonLevel w s n * d x n) :=
    summable_of_uniform_ennreal_tails _
      (fun x n => mul_nonneg (hHnonneg n) (hd x n)) hweightedTail
  refine ⟨w, hw1, hwmono, hwlim, hHlower, tendsto_atTop_mono hHlower hhlim,
    fun β hβ => all_temperature_summable s hs hsum w hwlim hβ,
    hbase, hweighted, ?_, ?_, hweightedTail⟩
  · exact continuous_of_uniform_ennreal_tails _
      (fun x n => mul_nonneg (hHnonneg n) (hd x n))
      (fun n => continuous_const.mul (hdcont n)) hweightedTail
  · intro x
    have hcost : (∑' n, ENNReal.ofReal (commonLevel w s n * d x n)) ≤
        (∑' n, ENNReal.ofReal (logarithmicLevel s n * d x n)) + (δ : ℝ≥0∞) := by
      simpa only [commonLevel, amplifiedEnergy, energyTerm, mul_assoc,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using hwcost x
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (hHnonneg n) (hd x n)) (hweighted x),
      ← ENNReal.ofReal_tsum_of_nonneg
        (fun n => mul_nonneg (hh n) (hd x n)) (hbase x),
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add
        (tsum_nonneg (fun n => mul_nonneg (hh n) (hd x n))) δ.coe_nonneg] at hcost
    exact (ENNReal.ofReal_le_ofReal_iff
      (add_nonneg (tsum_nonneg (fun n => mul_nonneg (hh n) (hd x n))) δ.coe_nonneg)).mp hcost

#print axioms exists_continuous_common_energy

end D5.S3.Quantum.Analysis.OrliczCommonEnergy
