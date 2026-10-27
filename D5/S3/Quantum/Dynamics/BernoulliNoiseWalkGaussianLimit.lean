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
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
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
      map_add' := by intro φ ψ; ext σ; change (if σ ∈ s then φ σ + ψ σ else 0) = _
                     split_ifs <;> simp
      map_smul' := by intro c φ; ext σ
                      change (if σ ∈ s then c • φ σ else 0) = _
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
  sorry

private lemma flip_commute (k j : ℕ) (φ : BernoulliSpace) :
    flipOperator k (flipOperator j φ) = flipOperator j (flipOperator k φ) := by
  sorry

private lemma flip_selfadjoint (k : ℕ) (φ ψ : BernoulliSpace) :
    inner ℂ (flipOperator k φ) ψ = inner ℂ φ (flipOperator k ψ) := by
  sorry

private lemma operators_eq_flip (k : ℕ) :
    creation k + annihilation k = (flipOperator k).toContinuousLinearMap := by
  sorry

private lemma projections (k : ℕ) :
    (R k).comp (R k) = R k ∧ (L k).comp (L k) = -L k ∧
    (R k).comp (L k) = 0 ∧ (L k).comp (R k) = 0 := by
  sorry

private lemma walk_support (φ : BernoulliSpace) (n : ℕ) (x : ℤ)
    (hx : (n : ℤ) < |x|) : walk φ n x = 0 := by
  sorry

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
  sorry

private lemma finite_tail_factorization (η : BernoulliSpace) (m n : ℕ) (hmn : m ≤ n)
    (hη : ∀ σ : Finset ℕ, ¬σ ⊆ Finset.range m → η σ = 0) (u : ℝ) :
    inner ℂ η (phaseProduct n u η) =
      (Real.cos u : ℂ) ^ (n - m) * inner ℂ η (phaseProduct m u η) := by
  sorry

private lemma cosine_gaussian_limit (t : ℝ) :
    Tendsto (fun n : ℕ => (Real.cos (t / Real.sqrt n) : ℂ) ^ n)
      atTop (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  sorry

private lemma finite_matrix_limit (η : BernoulliSpace) (m : ℕ)
    (hη : ∀ σ : Finset ℕ, ¬σ ⊆ Finset.range m → η σ = 0) (t : ℝ) :
    Tendsto (fun n : ℕ => inner ℂ η (phaseProduct n (t / Real.sqrt n) η))
      atTop (𝓝 ((‖η‖ ^ 2 : ℝ) * Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  sorry

private lemma finite_vectors_dense (φ : BernoulliSpace) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : BernoulliSpace, ∃ m : ℕ,
      (∀ σ : Finset ℕ, ¬σ ⊆ Finset.range m → η σ = 0) ∧ ‖φ - η‖ < ε := by
  sorry

private lemma matrix_lipschitz (n : ℕ) (u : ℝ) (φ η : BernoulliSpace) :
    ‖inner ℂ φ (phaseProduct n u φ) - inner ℂ η (phaseProduct n u η)‖ ≤
      (‖φ‖ + ‖η‖) * ‖φ - η‖ := by
  sorry

private lemma matrix_gaussian_limit (φ : BernoulliSpace) (hφ : ‖φ‖ = 1) (t : ℝ) :
    Tendsto (fun n : ℕ => inner ℂ φ (phaseProduct n (t / Real.sqrt n) φ))
      atTop (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  sorry

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
      one_mul, Complex.ofReal_zero, Complex.ofReal_one, zero_sub]
    convert matrix_gaussian_limit φ hφ t using 2 <;> congr 1 <;> ring
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hc f

end D5.S3.Quantum.Dynamics.BernoulliNoiseWalkGaussianLimit
