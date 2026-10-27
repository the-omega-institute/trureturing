/- GID: D5/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/BernoulliNoiseWalkGaussianLimit
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every localized quantum Bernoulli noise walk has the standard Gaussian limit. -/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-! The localized quantum Bernoulli noise walk of C. Wang, C. Wang, Y. Tang and S. Ren,
Advances in Mathematical Physics 2018, Article 2507265, DOI 10.1155/2018/2507265 (CC BY 4.0).
The creation and annihilation operators act on the finite-subset orthonormal basis.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit

abbrev BernoulliSpace := lp (fun _ : Finset ℕ => ℂ) 2
private def flipIndex (k : ℕ) : Equiv.Perm (Finset ℕ) where
  toFun σ := symmDiff σ {k}
  invFun σ := symmDiff σ {k}
  left_inv σ := symmDiff_symmDiff_cancel_right {k} σ
  right_inv σ := symmDiff_symmDiff_cancel_right {k} σ
private def flipOperator (k : ℕ) : BernoulliSpace →ₗᵢ[ℂ] BernoulliSpace where
  toFun φ := ⟨fun σ => φ (flipIndex k σ), memℓp_gen
    ((flipIndex k).summable_iff.mpr ((lp.memℓp φ).summable (by norm_num)))⟩
  map_add' φ ψ := by ext σ; rfl
  map_smul' c φ := by ext σ; rfl
  norm_map' φ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal)]
    congr 1
    exact (flipIndex k).tsum_eq (fun σ : Finset ℕ => ‖φ σ‖ ^ (2 : ENNReal).toReal)
private def mask (s : Set (Finset ℕ)) : BernoulliSpace →L[ℂ] BernoulliSpace := by
  classical
  exact LinearMap.mkContinuous
    { toFun := fun φ => ⟨fun σ => if σ ∈ s then φ σ else 0,
        (lp.memℓp φ).mono' (fun σ => by split_ifs <;> simp)⟩
      map_add' := by
        intro φ ψ
        ext σ
        change (if σ ∈ s then φ σ + ψ σ else 0) =
          (if σ ∈ s then φ σ else 0) + (if σ ∈ s then ψ σ else 0)
        split_ifs <;> simp
      map_smul' := by
        intro c φ
        ext σ
        change (if σ ∈ s then c * φ σ else 0) = c * (if σ ∈ s then φ σ else 0)
        split_ifs <;> simp }
    1 (fun φ => by
      rw [one_mul]
      apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro σ
      change ‖if σ ∈ s then φ σ else 0‖ ≤ ‖φ σ‖
      split_ifs <;> simp)
def annihilation (k : ℕ) : BernoulliSpace →L[ℂ] BernoulliSpace :=
  (mask {σ | k ∉ σ}).comp (flipOperator k).toContinuousLinearMap
def creation (k : ℕ) : BernoulliSpace →L[ℂ] BernoulliSpace :=
  (mask {σ | k ∈ σ}).comp (flipOperator k).toContinuousLinearMap

/-- The source's right operator, the positive flip projection. -/
def R (k : ℕ) : BernoulliSpace →L[ℂ] BernoulliSpace :=
  (1 / 2 : ℂ) • (creation k + annihilation k + ContinuousLinearMap.id ℂ BernoulliSpace)

/-- The source's left operator, the negative of the negative flip projection. -/
def L (k : ℕ) : BernoulliSpace →L[ℂ] BernoulliSpace :=
  (1 / 2 : ℂ) • (creation k + annihilation k - ContinuousLinearMap.id ℂ BernoulliSpace)

/-- Equations (53) and (16): the localized state and its walk recursion. -/
def walk (φ : BernoulliSpace) : ℕ → ℤ → BernoulliSpace
  | 0, x => if x = 0 then φ else 0
  | n + 1, x => R n (walk φ n (x - 1)) + L n (walk φ n (x + 1))

/-- The squared amplitude law of the position divided by the square root of time. -/
def walkLaw (φ : BernoulliSpace) (n : ℕ) : Measure ℝ :=
  ∑ x ∈ Finset.Icc (-(n : ℤ)) n,
    ENNReal.ofReal (‖walk φ n x‖ ^ 2) • Measure.dirac ((x : ℝ) / Real.sqrt n)

private def branch : ℕ → Finset ℕ → BernoulliSpace →L[ℂ] BernoulliSpace
  | 0, _ => ContinuousLinearMap.id ℂ BernoulliSpace
  | n + 1, σ => (if n ∈ σ then -L n else R n).comp (branch n σ)

private def displacement (n : ℕ) (σ : Finset ℕ) : ℤ := (n : ℤ) - 2 * σ.card

private def phaseStep (k : ℕ) (u : ℝ) : BernoulliSpace →L[ℂ] BernoulliSpace :=
  (Real.cos u : ℂ) • ContinuousLinearMap.id ℂ BernoulliSpace +
    ((Real.sin u : ℂ) * Complex.I) • (flipOperator k).toContinuousLinearMap

private def phaseProduct : ℕ → ℝ → BernoulliSpace →L[ℂ] BernoulliSpace
  | 0, _ => ContinuousLinearMap.id ℂ BernoulliSpace
  | n + 1, u => (phaseStep n u).comp (phaseProduct n u)

private lemma annihilation_basis (k : ℕ) (σ : Finset ℕ) :
    annihilation k (lp.single 2 σ (1 : ℂ)) =
      if k ∈ σ then lp.single 2 (σ.erase k) (1 : ℂ) else 0 := by
  sorry

private lemma creation_basis (k : ℕ) (σ : Finset ℕ) :
    creation k (lp.single 2 σ (1 : ℂ)) =
      if k ∈ σ then 0 else lp.single 2 (insert k σ) (1 : ℂ) := by
  sorry

private lemma flip_involution (k : ℕ) (φ : BernoulliSpace) :
    flipOperator k (flipOperator k φ) = φ := by
  ext σ
  change φ (symmDiff (symmDiff σ {k}) {k}) = φ σ
  rw [symmDiff_symmDiff_cancel_right]

private lemma flip_commute (k j : ℕ) (φ : BernoulliSpace) :
    flipOperator k (flipOperator j φ) = flipOperator j (flipOperator k φ) := by
  ext σ
  change φ (symmDiff (symmDiff σ {k}) {j}) = φ (symmDiff (symmDiff σ {j}) {k})
  rw [symmDiff_right_comm]

private lemma flip_selfadjoint (k : ℕ) (φ ψ : BernoulliSpace) :
    inner ℂ (flipOperator k φ) ψ = inner ℂ φ (flipOperator k ψ) := by
  have h := (flipOperator k).inner_map_map φ (flipOperator k ψ)
  rwa [flip_involution] at h

private lemma mask_apply (s : Set (Finset ℕ)) (φ : BernoulliSpace) (σ : Finset ℕ) :
    mask s φ σ = s.indicator φ σ := by
  classical
  rfl

private lemma operators_eq_flip (k : ℕ) :
    creation k + annihilation k = (flipOperator k).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro φ
  apply lp.ext
  funext σ
  rw [ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply,
    creation, annihilation, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    mask_apply, mask_apply]
  change ({τ : Finset ℕ | k ∈ τ}.indicator (fun τ => φ (flipIndex k τ))) σ +
    ({τ : Finset ℕ | k ∉ τ}.indicator (fun τ => φ (flipIndex k τ))) σ = φ (flipIndex k σ)
  by_cases h : k ∈ σ <;> simp only [Set.indicator_of_mem, Set.indicator_of_notMem,
    Set.mem_setOf_eq, h, not_true_eq_false, not_false_eq_true, add_zero, zero_add]

private lemma projections (k : ℕ) :
    (R k).comp (R k) = R k ∧ (L k).comp (L k) = -L k ∧
    (R k).comp (L k) = 0 ∧ (L k).comp (R k) = 0 := by
  have hr (φ : BernoulliSpace) :
      R k φ = (1 / 2 : ℂ) • (flipOperator k φ + φ) := by
    rw [R, operators_eq_flip]
    rfl
  have hl (φ : BernoulliSpace) :
      L k φ = (1 / 2 : ℂ) • (flipOperator k φ - φ) := by
    rw [L, operators_eq_flip]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    apply ContinuousLinearMap.ext
    intro φ
    simp only [ContinuousLinearMap.comp_apply, neg_apply,
      zero_apply, hr, hl, map_add, map_sub, map_smul, flip_involution]
    module

private lemma walk_support (φ : BernoulliSpace) (n : ℕ) (x : ℤ)
    (hx : (n : ℤ) < |x|) : walk φ n x = 0 := by
  induction n generalizing x with
  | zero =>
    have h : x ≠ 0 := by intro h; subst x; norm_num at hx
    exact if_neg h
  | succ n ih =>
    have hm : (n : ℤ) < |x - 1| := by
      have hh := abs_add_le (x - 1) 1
      rw [sub_add_cancel, abs_one] at hh
      omega
    have hp : (n : ℤ) < |x + 1| := by
      have hh := abs_sub (x + 1) 1
      rw [add_sub_cancel_right, abs_one] at hh
      omega
    rw [walk, ih (x - 1) hm, ih (x + 1) hp, map_zero, map_zero, add_zero]

private lemma walk_expansion (φ : BernoulliSpace) (n : ℕ) (x : ℤ) :
    walk φ n x =
      ∑ σ ∈ (Finset.range n).powerset.filter (fun σ => displacement n σ = x),
        ((-1 : ℂ) ^ σ.card) • branch n σ φ := by
  sorry

private lemma walk_exact_law (φ : BernoulliSpace) (n : ℕ) (x : ℤ) :
    ‖walk φ n x‖ ^ 2 =
      ∑ σ ∈ (Finset.range n).powerset.filter (fun σ => displacement n σ = x),
        ‖branch n σ φ‖ ^ 2 := by
  sorry

private lemma branch_parseval (φ : BernoulliSpace) (n : ℕ) :
    ∑ σ ∈ (Finset.range n).powerset, ‖branch n σ φ‖ ^ 2 = ‖φ‖ ^ 2 := by
  sorry

private lemma walk_mass (φ : BernoulliSpace) (n : ℕ) :
    ∑ x ∈ Finset.Icc (-(n : ℤ)) n, ‖walk φ n x‖ ^ 2 = ‖φ‖ ^ 2 := by
  sorry

private lemma walkLaw_probability (φ : BernoulliSpace) (hφ : ‖φ‖ = 1) (n : ℕ) :
    IsProbabilityMeasure (walkLaw φ n) := by
  sorry

private lemma charFun_formula (φ : BernoulliSpace) (n : ℕ) (t : ℝ) :
    charFun (walkLaw φ n) t =
      inner ℂ φ (phaseProduct n (t / Real.sqrt n) φ) := by
  sorry

private lemma phaseProduct_isometry (n : ℕ) (u : ℝ) (φ : BernoulliSpace) :
    ‖phaseProduct n u φ‖ = ‖φ‖ := by
  have hs (k : ℕ) (ψ : BernoulliSpace) : ‖phaseStep k u ψ‖ = ‖ψ‖ := by
    apply (LinearMap.norm_map_iff_inner_map_map (phaseStep k u)).mpr ?_ ψ
    intro η ζ
    change inner ℂ ((Real.cos u : ℂ) • η +
      ((Real.sin u : ℂ) * Complex.I) • flipOperator k η)
      ((Real.cos u : ℂ) • ζ +
        ((Real.sin u : ℂ) * Complex.I) • flipOperator k ζ) = inner ℂ η ζ
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      map_mul, Complex.conj_ofReal, Complex.conj_I, (flipOperator k).inner_map_map,
      flip_selfadjoint]
    have hc : (Real.cos u : ℂ) ^ 2 + (Real.sin u : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq u
    calc
      _ = ((Real.cos u : ℂ) ^ 2 + (Real.sin u : ℂ) ^ 2) * inner ℂ η ζ := by
        ring_nf
        simp only [Complex.I_sq]
        ring
      _ = inner ℂ η ζ := by rw [hc, one_mul]
  induction n with
  | zero => rfl
  | succ n ih =>
    change ‖phaseStep n u (phaseProduct n u φ)‖ = ‖φ‖
    rw [hs, ih]

private lemma flip_subset_iff (k m : ℕ) (hk : k < m) (σ : Finset ℕ) :
    flipIndex k σ ⊆ Finset.range m ↔ σ ⊆ Finset.range m := by
  have h (τ : Finset ℕ) (hτ : τ ⊆ Finset.range m) :
      flipIndex k τ ⊆ Finset.range m := by
    intro j hj
    change j ∈ symmDiff τ {k} at hj
    rcases Finset.mem_symmDiff.mp hj with hj | hj
    · exact hτ hj.1
    · have hjk : j = k := Finset.mem_singleton.mp hj.1
      subst j
      exact Finset.mem_range.mpr hk
  constructor
  · intro hσ
    have hh := h (flipIndex k σ) hσ
    change symmDiff (symmDiff σ {k}) {k} ⊆ Finset.range m at hh
    rwa [symmDiff_symmDiff_cancel_right] at hh
  · exact h σ

private lemma phaseProduct_support (η : BernoulliSpace) (m n : ℕ)
    (hnm : n ≤ m) (hη : ∀ σ : Finset ℕ, ¬σ ⊆ Finset.range m → η σ = 0) (u : ℝ) :
    ∀ σ : Finset ℕ, ¬σ ⊆ Finset.range m → phaseProduct n u η σ = 0 := by
  revert hnm
  induction n with
  | zero => intro _; exact hη
  | succ n ih =>
    intro hnm σ hσ
    have hn : n < m := lt_of_lt_of_le (Nat.lt_succ_self n) hnm
    have hf : ¬flipIndex n σ ⊆ Finset.range m :=
      fun h => hσ ((flip_subset_iff n m hn σ).mp h)
    change (Real.cos u : ℂ) * phaseProduct n u η σ +
      ((Real.sin u : ℂ) * Complex.I) * phaseProduct n u η (flipIndex n σ) = 0
    rw [ih (Nat.le_of_succ_le hnm) σ hσ, ih (Nat.le_of_succ_le hnm) _ hf]
    simp only [mul_zero, add_zero]

private lemma tail_cross_zero (η : BernoulliSpace) (m n : ℕ) (hmn : m ≤ n)
    (hη : ∀ σ : Finset ℕ, ¬σ ⊆ Finset.range m → η σ = 0) (u : ℝ) :
    inner ℂ η (flipOperator n (phaseProduct n u η)) = 0 := by
  have hηn : ∀ σ : Finset ℕ, ¬σ ⊆ Finset.range n → η σ = 0 := by
    intro σ hσ
    exact hη σ (fun h => hσ (h.trans (Finset.range_mono hmn)))
  rw [← flip_selfadjoint, lp.inner_eq_tsum]
  suffices hz : ∀ σ : Finset ℕ,
      inner ℂ (flipOperator n η σ) (phaseProduct n u η σ) = 0 by
    simp only [hz, tsum_zero]
  intro σ
  by_cases hσ : σ ⊆ Finset.range n
  · have hnσ : n ∉ σ := fun h => (Nat.lt_irrefl n) (Finset.mem_range.mp (hσ h))
    have hflip : ¬flipIndex n σ ⊆ Finset.range m := by
      intro hh
      have hn : n ∈ flipIndex n σ := by
        change n ∈ symmDiff σ {n}
        exact Finset.mem_symmDiff.mpr (Or.inr ⟨Finset.mem_singleton_self n, hnσ⟩)
      have := Finset.mem_range.mp (hh hn)
      omega
    change inner ℂ (η (flipIndex n σ)) (phaseProduct n u η σ) = 0
    rw [hη _ hflip, inner_zero_left]
  · rw [phaseProduct_support η n n le_rfl hηn u σ hσ, inner_zero_right]

private lemma finite_tail_factorization (η : BernoulliSpace) (m n : ℕ) (hmn : m ≤ n)
    (hη : ∀ σ : Finset ℕ, ¬σ ⊆ Finset.range m → η σ = 0) (u : ℝ) :
    inner ℂ η (phaseProduct n u η) =
      (Real.cos u : ℂ) ^ (n - m) * inner ℂ η (phaseProduct m u η) := by
  induction n, hmn using Nat.le_induction with
  | base => simp only [Nat.sub_self, pow_zero, one_mul]
  | succ n hmn ih =>
    change inner ℂ η ((Real.cos u : ℂ) • phaseProduct n u η +
      ((Real.sin u : ℂ) * Complex.I) • flipOperator n (phaseProduct n u η)) = _
    rw [inner_add_right, inner_smul_right, inner_smul_right,
      tail_cross_zero η m n hmn hη u, mul_zero, add_zero, ih]
    have hn : n + 1 - m = (n - m) + 1 := by omega
    rw [hn, pow_succ]
    ring

private lemma cosine_gaussian_limit (t : ℝ) :
    Tendsto (fun n : ℕ => (Real.cos (t / Real.sqrt n) : ℂ) ^ n)
      atTop (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  let p : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  let ν : Measure ℝ := bernoulliMeasure 1 (-1) p
  have h0 : (∫ x : ℝ, x ∂ν) = 0 := by
    change (∫ x : ℝ, x ∂bernoulliMeasure 1 (-1) p) = 0
    rw [integral_bernoulliMeasure]
    norm_num [p]
  have h1 : (∫ x : ℝ, x ^ 2 ∂ν) = 1 := by
    change (∫ x : ℝ, x ^ 2 ∂bernoulliMeasure 1 (-1) p) = 1
    rw [integral_bernoulliMeasure]
    norm_num [p]
  have hc (u : ℝ) : charFun ν u = (Real.cos u : ℂ) := by
    rw [charFun_apply_real]
    change (∫ x : ℝ, Complex.exp ((u : ℂ) * x * Complex.I)
      ∂bernoulliMeasure 1 (-1) p) = _
    rw [integral_bernoulliMeasure]
    simp only [p, Complex.ofReal_one, Complex.ofReal_neg, mul_one, mul_neg_one]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.real_smul]
    norm_num
    ring
  have hh := tendsto_charFun_inv_sqrt_mul_pow (P := ν) (X := id)
    measurable_id.aemeasurable h0 h1 t
  simpa only [Measure.map_id, hc, div_eq_inv_mul] using hh

private lemma phaseProduct_continuous (n : ℕ) (η : BernoulliSpace) :
    Continuous (fun u : ℝ => phaseProduct n u η) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    change Continuous (fun u : ℝ => (Real.cos u : ℂ) • phaseProduct n u η +
      ((Real.sin u : ℂ) * Complex.I) • flipOperator n (phaseProduct n u η))
    exact ((Complex.continuous_ofReal.comp Real.continuous_cos).smul ih).add
      (((Complex.continuous_ofReal.comp Real.continuous_sin).mul continuous_const).smul
        ((flipOperator n).continuous.comp ih))

private lemma phaseProduct_zero (n : ℕ) (η : BernoulliSpace) :
    phaseProduct n 0 η = η := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (Real.cos 0 : ℂ) • phaseProduct n 0 η +
      ((Real.sin 0 : ℂ) * Complex.I) • flipOperator n (phaseProduct n 0 η) = η
    simpa only [Real.cos_zero, Real.sin_zero, Complex.ofReal_one, Complex.ofReal_zero,
      one_smul, zero_mul, zero_smul, add_zero] using ih

private lemma finite_matrix_limit (η : BernoulliSpace) (m : ℕ)
    (hη : ∀ σ : Finset ℕ, ¬σ ⊆ Finset.range m → η σ = 0) (t : ℝ) :
    Tendsto (fun n : ℕ => inner ℂ η (phaseProduct n (t / Real.sqrt n) η))
      atTop (𝓝 ((‖η‖ ^ 2 : ℝ) * Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  have hu : Tendsto (fun n : ℕ => t / Real.sqrt n) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
        tendsto_natCast_atTop_atTop)).const_mul t
  have hc : Tendsto (fun n : ℕ => (Real.cos (t / Real.sqrt n) : ℂ)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.cos_zero, Complex.ofReal_one] using
      ((Complex.continuous_ofReal.comp Real.continuous_cos).tendsto 0).comp hu
  have hp : Tendsto (fun n : ℕ => (Real.cos (t / Real.sqrt n) : ℂ) ^ (n - m))
      atTop (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
    have hh := (cosine_gaussian_limit t).div (hc.pow m) (by simp)
    simp only [one_pow, div_one] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop m, hc.eventually_ne (by norm_num : (1 : ℂ) ≠ 0)]
      with n hn hn0
    change (Real.cos (t / Real.sqrt n) : ℂ) ^ n /
      (Real.cos (t / Real.sqrt n) : ℂ) ^ m = _
    rw [pow_sub₀ _ hn0 hn, div_eq_mul_inv]
  have hf : Tendsto (fun n : ℕ => inner ℂ η (phaseProduct m (t / Real.sqrt n) η))
      atTop (𝓝 ((‖η‖ ^ 2 : ℝ) : ℂ)) := by
    have hh := (((continuous_const : Continuous (fun _ : ℝ => η)).inner
      (𝕜 := ℂ) (phaseProduct_continuous m η)).tendsto 0).comp hu
    convert hh using 1 <;> simp only [Function.comp_def, phaseProduct_zero,
      inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    congr 1
  have hh := hp.mul hf
  rw [mul_comm] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop m] with n hn
  exact (finite_tail_factorization η m n hn hη (t / Real.sqrt n)).symm

private lemma finite_vectors_dense (φ : BernoulliSpace) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : BernoulliSpace, ∃ m : ℕ,
      (∀ σ : Finset ℕ, ¬σ ⊆ Finset.range m → η σ = 0) ∧ ‖φ - η‖ < ε := by
  classical
  obtain ⟨s, hs⟩ := ((lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) φ).eventually
    (Metric.ball_mem_nhds φ hε)).exists
  let η : BernoulliSpace := ∑ σ ∈ s, lp.single 2 σ (φ σ)
  let m : ℕ := (s.biUnion id).sup id + 1
  refine ⟨η, m, ?_, ?_⟩
  · intro σ hσ
    change (∑ τ ∈ s, lp.single 2 τ (φ τ)) σ = 0
    rw [lp.coeFn_sum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro τ hτ
    apply lp.single_apply_ne
    intro he
    subst τ
    apply hσ
    intro j hj
    apply Finset.mem_range.mpr
    have hjb : j ∈ s.biUnion id := Finset.mem_biUnion.mpr ⟨σ, hτ, hj⟩
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hjb)
  · change dist η φ < ε at hs
    simpa only [dist_eq_norm, norm_sub_rev] using hs

private lemma matrix_lipschitz (n : ℕ) (u : ℝ) (φ η : BernoulliSpace) :
    ‖inner ℂ φ (phaseProduct n u φ) - inner ℂ η (phaseProduct n u η)‖ ≤
      (‖φ‖ + ‖η‖) * ‖φ - η‖ := by
  have he : inner ℂ φ (phaseProduct n u φ) - inner ℂ η (phaseProduct n u η) =
      inner ℂ (φ - η) (phaseProduct n u φ) +
      inner ℂ η (phaseProduct n u (φ - η)) := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  rw [he]
  calc
    _ ≤ ‖inner ℂ (φ - η) (phaseProduct n u φ)‖ +
        ‖inner ℂ η (phaseProduct n u (φ - η))‖ := norm_add_le _ _
    _ ≤ ‖φ - η‖ * ‖phaseProduct n u φ‖ +
        ‖η‖ * ‖phaseProduct n u (φ - η)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ = (‖φ‖ + ‖η‖) * ‖φ - η‖ := by
      rw [phaseProduct_isometry, phaseProduct_isometry]
      ring

private lemma matrix_gaussian_limit (φ : BernoulliSpace) (hφ : ‖φ‖ = 1) (t : ℝ) :
    Tendsto (fun n : ℕ => inner ℂ φ (phaseProduct n (t / Real.sqrt n) φ))
      atTop (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  let z : ℂ := Complex.exp (-(t : ℂ) ^ 2 / 2)
  have hz : ‖z‖ ≤ 1 := by
    have he : charFun (gaussianReal 0 1) t = z := by
      simp only [charFun_gaussianReal, NNReal.coe_one, Complex.ofReal_zero,
        Complex.ofReal_one, mul_zero, zero_mul, one_mul, zero_sub]
      congr 1
      ring
    rw [← he]
    exact norm_charFun_le_one t
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ : ℝ := min 1 (ε / 12)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  obtain ⟨η, m, hη, hd⟩ := finite_vectors_dense φ δ hδ
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε / 12 := min_le_right _ _
  have hη2 : ‖η‖ ≤ 2 := by
    have hh := norm_le_norm_add_norm_sub φ η
    rw [hφ] at hh
    linarith
  have hdiff : |‖η‖ - 1| ≤ ‖φ - η‖ := by
    simpa only [hφ, abs_sub_comm] using abs_norm_sub_norm_le φ η
  have hsq : |‖η‖ ^ 2 - 1| ≤ 3 * ‖φ - η‖ := by
    calc
      |‖η‖ ^ 2 - 1| = |‖η‖ - 1| * (‖η‖ + 1) := by
        rw [← abs_of_nonneg (show 0 ≤ ‖η‖ + 1 by positivity), ← abs_mul]
        congr 1
        ring
      _ ≤ ‖φ - η‖ * (‖η‖ + 1) :=
        mul_le_mul_of_nonneg_right hdiff (by positivity)
      _ ≤ 3 * ‖φ - η‖ := by nlinarith [norm_nonneg (φ - η)]
  have ht : ‖((‖η‖ ^ 2 : ℝ) : ℂ) * z - z‖ ≤ 3 * ‖φ - η‖ := by
    rw [← sub_one_mul, norm_mul]
    calc
      _ ≤ ‖((‖η‖ ^ 2 : ℝ) : ℂ) - 1‖ * 1 :=
        mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ = |‖η‖ ^ 2 - 1| := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, mul_one]
      _ ≤ 3 * ‖φ - η‖ := hsq
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (finite_matrix_limit η m hη t)
    (ε / 3) (by positivity)
  refine ⟨N, ?_⟩
  intro n hn
  have ha := matrix_lipschitz n (t / Real.sqrt n) φ η
  rw [hφ] at ha
  have ha' : ‖inner ℂ φ (phaseProduct n (t / Real.sqrt n) φ) -
      inner ℂ η (phaseProduct n (t / Real.sqrt n) η)‖ ≤ 3 * ‖φ - η‖ := by
    nlinarith [norm_nonneg (φ - η)]
  have hb : ‖inner ℂ η (phaseProduct n (t / Real.sqrt n) η) -
      ((‖η‖ ^ 2 : ℝ) : ℂ) * z‖ < ε / 3 := by
    simpa only [dist_eq_norm] using hN n hn
  rw [dist_eq_norm]
  have hc := norm_sub_le_norm_sub_add_norm_sub
    (inner ℂ φ (phaseProduct n (t / Real.sqrt n) φ))
    (inner ℂ η (phaseProduct n (t / Real.sqrt n) η)) z
  have hc' := norm_sub_le_norm_sub_add_norm_sub
    (inner ℂ η (phaseProduct n (t / Real.sqrt n) η))
    (((‖η‖ ^ 2 : ℝ) : ℂ) * z) z
  change ‖inner ℂ φ (phaseProduct n (t / Real.sqrt n) φ) - z‖ < ε
  linarith

/-- Every unit localized initial state has the classical standard Gaussian scaling limit. -/
theorem result (φ : BernoulliSpace) (hφ : ‖φ‖ = 1) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ y, f y ∂(walkLaw φ n)) atTop
      (𝓝 (∫ y, f y ∂(gaussianReal 0 1))) := by
  let μ : ℕ → ProbabilityMeasure ℝ := fun n => ⟨walkLaw φ n, walkLaw_probability φ hφ n⟩
  let γ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  have hc : Tendsto μ atTop (𝓝 γ) := by
    apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
    intro t
    change Tendsto (fun n => charFun (walkLaw φ n) t) atTop
      (𝓝 (charFun (gaussianReal 0 1) t))
    simp only [charFun_formula, charFun_gaussianReal, zero_mul, mul_zero,
      NNReal.coe_one, Complex.ofReal_zero, Complex.ofReal_one, one_mul, zero_sub]
    convert matrix_gaussian_limit φ hφ t using 2 <;> congr 1 <;> ring
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hc f

end D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit
