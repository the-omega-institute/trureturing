/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Math.LinearAlgebra.Majorization
public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Math.MeasureTheory.DiracSum
public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.Order.Strassen.Basic

/-!
# Discrete Strassen's theorem (uniform equal-cardinality case)

This file handles the discrete case of **Strassen's theorem** for two finitely-supported
probability laws `μ, ν` on `ℝ` in **convex order** with a common atom count and uniform weights
`1/n`: Such laws admit an explicit **martingale coupling**, built from a **bistochastic martingale
matrix**.

Given atoms `x₁, …, xₙ` of `μ` and `y₁, …, yₙ` of `ν`, the Hardy–Littlewood–Pólya majorization
theorem produces a matrix `T : Fin n × Fin n → ℝ` with

* `∀ i, pᵢ ≠ 0 → ∑ⱼ T i j = 1` — active rows are probability distributions,
* `∀ i, pᵢ ≠ 0 → ∑ⱼ T i j · yⱼ = xᵢ` — active-row conditional mean is `xᵢ`,
* `∀ j, ∑ᵢ pᵢ · T i j = qⱼ` — marginal constraint (`ν` is the pushforward).

Setting `π({(xᵢ, yⱼ)}) = pᵢ · T i j` yields the martingale coupling.

## Main definitions

* `DiscreteLaw` — finite-support real-valued probability law represented by atoms and weights.
* `DiscreteLaw.toProbDist` — embedding into `ProbDist ℝ` via a finite sum of Diracs.
* `DiscreteLaw.ConvexOrder` — finitary convex order (Jensen on atoms).
* `BistochasticMartingaleMatrix` — the transition matrix `T` above.

## Main statements

* `discrete_martingale_matrix_exists_uniform` — convex order on finitely-supported laws with a
  common atom count and uniform weights `1/n` yields a bistochastic martingale matrix.
* `DiscreteLaw.exists_martingaleCoupling_uniform` — from the matrix, build `π : ProbDist (ℝ × ℝ)`
  with `IsMartingaleCoupling p.toProbDist q.toProbDist π`.

## Notes

This is the uniform equal-cardinality case produced by the quantile atomization `condMeanAtomize`.
The general statement for arbitrary finite support and nonuniform weights is
`DiscreteLaw.exists_martingaleCoupling`, in `Strassen/DiscreteGeneral.lean`.

## References

* Strassen, V. 1965. “The Existence of Probability Measures with Given Marginals.” *The Annals of
  Mathematical Statistics* 36 (2): 423–39. [https://doi.org/10.1214/aoms/1177700153](https://doi.org/10.1214/aoms/1177700153).

## Tags

strassen, convex order, martingale coupling, doubly stochastic, majorization
-/

@[expose] public section

open MeasureTheory Set Finset BigOperators

namespace Econlib.Probability

/-- A finitely-supported real-valued probability law specified by atoms and weights. -/
structure DiscreteLaw where
  /-- The number of atoms. -/
  n : ℕ
  /-- Locations of atoms. -/
  atom : Fin n → ℝ
  /-- Probability weights on each atom. -/
  weight : Fin n → ℝ
  /-- Weights are non-negative. -/
  weight_nonneg : ∀ i, 0 ≤ weight i
  /-- Weights sum to one. -/
  weight_sum : ∑ i, weight i = 1

namespace DiscreteLaw

/-- Embedding of a discrete law into `ProbDist ℝ` as a finite weighted sum of Diracs. -/
noncomputable def toProbDist (p : DiscreteLaw) : ProbDist ℝ :=
  ⟨∑ i, ENNReal.ofReal (p.weight i) • Measure.dirac (p.atom i), by
    constructor
    simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ,
      Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => p.weight_nonneg i), p.weight_sum]
    simp⟩

@[simp] lemma toProbDist_toMeasure (p : DiscreteLaw) :
    p.toProbDist.toMeasure = ∑ i, ENNReal.ofReal (p.weight i) • Measure.dirac (p.atom i) :=
  rfl

/-- If all atoms of a discrete law lie in a measurable set `s`, then the law is supported on `s`. -/
lemma toProbDist_supportsOn_of_atoms_mem (p : DiscreteLaw) {s : Set ℝ}
    (hs : MeasurableSet s) (hatoms : ∀ i, p.atom i ∈ s) :
    p.toProbDist.supportsOn s := by
  unfold ProbDist.supportsOn
  rw [toProbDist_toMeasure]
  simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs]
  have h_ind : ∀ i, (s.indicator (1 : ℝ → ENNReal) (p.atom i)) = 1 := fun i => by
    simp [Set.indicator_of_mem (hatoms i)]
  simp_rw [h_ind, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => p.weight_nonneg i), p.weight_sum,
    ENNReal.ofReal_one]

/-- The mean of the discrete law: `∑ i, weight i · atom i`. -/
noncomputable def mean (p : DiscreteLaw) : ℝ := ∑ i, p.weight i * p.atom i

/-- Jensen-form convex order for discrete laws: Every convex function gets weakly larger
expectation under `q` than under `p`. -/
def ConvexOrder (p q : DiscreteLaw) : Prop :=
  ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ →
    ∑ i, p.weight i * φ (p.atom i) ≤ ∑ j, q.weight j * φ (q.atom j)

/-- Convex order on discrete laws forces equal means: Testing against `id` and `-id` (both convex)
gives `p.mean ≤ q.mean ≤ p.mean`. -/
lemma ConvexOrder.mean_eq {p q : DiscreteLaw} (h : p.ConvexOrder q) : p.mean = q.mean := by
  have hconv_id : ConvexOn ℝ Set.univ (id : ℝ → ℝ) := convexOn_id convex_univ
  have hconv_neg : ConvexOn ℝ Set.univ (fun x : ℝ => -x) := (concaveOn_id convex_univ).neg
  have h_le : p.mean ≤ q.mean := by
    simpa [DiscreteLaw.mean] using h id hconv_id
  have h_ge : q.mean ≤ p.mean := by
    have hneg := h (fun x => -x) hconv_neg
    have hsp : ∑ i, p.weight i * (- p.atom i) = -p.mean := by
      simp [DiscreteLaw.mean, mul_neg, Finset.sum_neg_distrib]
    have hsq : ∑ j, q.weight j * (- q.atom j) = -q.mean := by
      simp [DiscreteLaw.mean, mul_neg, Finset.sum_neg_distrib]
    rw [hsp, hsq] at hneg
    linarith
  linarith

/-! ### Uniform-weight helper

A convenience constructor for `DiscreteLaw` with `n` atoms each carrying probability `1/n`. -/

/-- Uniform-weight discrete law with `n` atoms at positions `x k`, each atom carrying weight
`1/n`. -/
noncomputable def uniform (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) : DiscreteLaw where
  n := n
  atom := x
  weight := fun _ => (1 : ℝ) / n
  weight_nonneg := fun _ => by positivity
  weight_sum := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp

@[simp] lemma uniform_n {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    (uniform n hn x).n = n := rfl

@[simp] lemma uniform_atom {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (i : Fin n) :
    (uniform n hn x).atom i = x i := rfl

@[simp] lemma uniform_weight {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (i : Fin n) :
    (uniform n hn x).weight i = (1 : ℝ) / n := rfl

/-- The mean of a uniform-weight discrete law is the arithmetic mean of its atoms. -/
lemma uniform_mean {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    (uniform n hn x).mean = (∑ i, x i) / n := by
  simp only [mean, uniform]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end DiscreteLaw

/-- A **bistochastic martingale matrix** transporting `p` to `q`:

* positive-weight rows are probability distributions,
* each positive-weight row's `q.atom`-average equals the corresponding `p.atom`,
* the column marginal reproduces `q.weight`.

Rows with `p.weight i = 0` are irrelevant to the transported measure
`π({(p.atom i, q.atom j)}) = p.weight i * T i j`, so we do not impose Markov or martingale
constraints on them. -/
structure BistochasticMartingaleMatrix (p q : DiscreteLaw) where
  /-- Transition probabilities: `T i j` is the conditional probability of `q.atom j` given
  `p.atom i`. -/
  T : Fin p.n → Fin q.n → ℝ
  /-- Entries are non-negative. -/
  nonneg : ∀ i j, 0 ≤ T i j
  /-- Positive-weight rows sum to one (Markov property on the transported support). -/
  row_sum : ∀ i, p.weight i ≠ 0 → ∑ j, T i j = 1
  /-- Positive-weight rows have the prescribed conditional mean. -/
  mean_eq : ∀ i, p.weight i ≠ 0 → ∑ j, T i j * q.atom j = p.atom i
  /-- Column marginal reproduces `q.weight` (pushforward to the target). -/
  col_marginal : ∀ j, ∑ i, p.weight i * T i j = q.weight j

/-- Build a `BistochasticMartingaleMatrix` from a square doubly stochastic matrix on `Fin p.n` once
the target law is reindexed to the same cardinality and both laws have uniform weights. This
isolates the remaining discrete Strassen gap to the majorization statement `D *ᵥ y = x`. -/
lemma BistochasticMartingaleMatrix.nonempty_of_doublyStochastic
    {p q : DiscreteLaw} (hn : p.n = q.n)
    (hp_uniform : ∀ i, p.weight i = (1 : ℝ) / p.n)
    (hq_uniform : ∀ j, q.weight j = (1 : ℝ) / q.n)
    (D : Matrix (Fin p.n) (Fin p.n) ℝ)
    (hD : D ∈ doublyStochastic ℝ (Fin p.n))
    (hmean : Matrix.mulVec D (q.atom ∘ (Fin.castOrderIso hn).toEquiv) = p.atom) :
    Nonempty (BistochasticMartingaleMatrix p q) := by
  let e : Fin p.n ≃ Fin q.n := (Fin.castOrderIso hn).toEquiv
  refine ⟨{
    T := fun i j => D i (e.symm j)
    nonneg := ?_
    row_sum := ?_
    mean_eq := ?_
    col_marginal := ?_
  }⟩
  · intro i j
    simpa [e] using (nonneg_of_mem_doublyStochastic hD (i := i) (j := e.symm j))
  · intro i _
    calc
      ∑ j, D i (e.symm j)
          = ∑ j : Fin p.n, D i j := by
            simpa using (Equiv.sum_comp e.symm (fun j : Fin p.n => D i j))
      _ = 1 := sum_row_of_mem_doublyStochastic hD i
  · intro i _
    have hi_mean : Matrix.mulVec D (q.atom ∘ e) i = p.atom i := by
      simpa [e] using congrArg (fun v => v i) hmean
    calc
      ∑ j, D i (e.symm j) * q.atom j
          = ∑ j : Fin p.n, D i j * q.atom (e j) := by
            simpa using
              (Equiv.sum_comp e (fun j : Fin q.n => D i (e.symm j) * q.atom j)).symm
      _ = Matrix.mulVec D (q.atom ∘ e) i := by
        simp [Matrix.mulVec, dotProduct, e]
      _ = p.atom i := hi_mean
  · intro j
    calc
      ∑ i, p.weight i * D i (e.symm j)
          = ∑ i : Fin p.n, ((1 : ℝ) / p.n) * D i (e.symm j) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [hp_uniform i]
      _ = (1 : ℝ) / p.n * ∑ i : Fin p.n, D i (e.symm j) := by rw [← Finset.mul_sum]
      _ = (1 : ℝ) / p.n := by rw [sum_col_of_mem_doublyStochastic hD (e.symm j), mul_one]
      _ = q.weight j := by
        rw [hq_uniform j]
        simp [hn]

private lemma convexOrder_unweighted_of_uniform
    {p q : DiscreteLaw} (hn_pos : 0 < p.n) (hn : p.n = q.n)
    (hp_uniform : ∀ i, p.weight i = (1 : ℝ) / p.n)
    (hq_uniform : ∀ j, q.weight j = (1 : ℝ) / q.n)
    (h : DiscreteLaw.ConvexOrder p q) :
    ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ ->
      ∑ i, φ (p.atom i) ≤ ∑ j, φ (q.atom j) := by
  intro φ hφ
  have hcx := h φ hφ
  have hc : 0 < (1 : ℝ) / p.n := by
    positivity
  have hp_sum :
      ∑ i, p.weight i * φ (p.atom i) = ((1 : ℝ) / p.n) * ∑ i, φ (p.atom i) := by
    simp_rw [hp_uniform]
    rw [Finset.mul_sum]
  have hq_sum :
      ∑ j, q.weight j * φ (q.atom j) = ((1 : ℝ) / p.n) * ∑ j, φ (q.atom j) := by
    simp_rw [hq_uniform]
    rw [Finset.mul_sum]
    simp [hn]
  rw [hp_sum, hq_sum] at hcx
  nlinarith

private lemma sum_eq_of_uniform_mean_eq
    {p q : DiscreteLaw} (hn_pos : 0 < p.n) (hn : p.n = q.n)
    (hp_uniform : ∀ i, p.weight i = (1 : ℝ) / p.n)
    (hq_uniform : ∀ j, q.weight j = (1 : ℝ) / q.n)
    (hmean : p.mean = q.mean) :
    ∑ i, p.atom i = ∑ j, q.atom j := by
  have hp_mean :
      p.mean = ((1 : ℝ) / p.n) * ∑ i, p.atom i := by
    simp [DiscreteLaw.mean, hp_uniform, Finset.mul_sum]
  have hq_mean :
      q.mean = ((1 : ℝ) / p.n) * ∑ j, q.atom j := by
    simp [DiscreteLaw.mean, hq_uniform, Finset.mul_sum, hn]
  rw [hp_mean, hq_mean] at hmean
  have hc : 0 < (1 : ℝ) / p.n := by
    positivity
  nlinarith

/-- **Discrete Hardy–Littlewood–Pólya — uniform equal-cardinality case.** Convex-order domination
between two finitely-supported laws that carry the same number of atoms and uniform weights `1/n`
yields a bistochastic martingale matrix.

This is the special case used by the continuous Strassen proof, where the quantile atomization
`condMeanAtomize` produces uniform, equal-cardinality laws. The general discrete Strassen theorem —
arbitrary finite support with nonuniform weights — is `DiscreteLaw.exists_martingaleCoupling`. -/
theorem discrete_martingale_matrix_exists_uniform (p q : DiscreteLaw)
    (hn_pos : 0 < p.n) (hn : p.n = q.n)
    (hp_uniform : ∀ i, p.weight i = (1 : ℝ) / p.n)
    (hq_uniform : ∀ j, q.weight j = (1 : ℝ) / q.n)
    (h : DiscreteLaw.ConvexOrder p q) :
    Nonempty (BistochasticMartingaleMatrix p q) := by
  have hmean_eq : p.mean = q.mean := DiscreteLaw.ConvexOrder.mean_eq h
  -- Base case: `p` has exactly one atom. Then `p.atom i = p.mean = q.mean` for the unique
  -- `i`, and `T i j := q.weight j` satisfies all four properties trivially.
  by_cases hp1 : p.n = 1
  · refine ⟨?_⟩
    -- Singleton lemma: `Fin p.n = {i}` for any `i`.
    have hsingle : ∀ i : Fin p.n, (Finset.univ : Finset (Fin p.n)) = {i} := by
      intro i
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun j _ => ?_⟩
      have hj : j.val < p.n := j.isLt
      have hi : i.val < p.n := i.isLt
      exact Fin.ext (by omega)
    have hp_weight_one : ∀ i : Fin p.n, p.weight i = 1 := fun i => by
      rw [← p.weight_sum, hsingle i, Finset.sum_singleton]
    have hp_atom_eq_mean : ∀ i : Fin p.n, p.atom i = p.mean := fun i => by
      unfold DiscreteLaw.mean
      rw [hsingle i, Finset.sum_singleton, hp_weight_one i, one_mul]
    exact {
      T := fun _ j => q.weight j
      nonneg := fun _ j => q.weight_nonneg j
      row_sum := fun _ _ => q.weight_sum
      mean_eq := fun i _ => by
        show ∑ j, q.weight j * q.atom j = p.atom i
        rw [hp_atom_eq_mean i, hmean_eq]; rfl
      col_marginal := fun j => by
        show ∑ i, p.weight i * q.weight j = q.weight j
        rw [← Finset.sum_mul, p.weight_sum, one_mul]
    }
  · -- General case (`p.n ≥ 2`): classical Hardy–Littlewood–Pólya. Requires a separate
    -- majorization theorem converting the scalar convex-order inequalities on the
    -- equally-weighted atoms into a doubly stochastic matrix acting on the target atom vector.
    let y : Fin p.n → ℝ := q.atom ∘ (Fin.castOrderIso hn).toEquiv
    -- Reindexing `y` back onto `q.atom` along the `Fin p.n ≃ Fin q.n` cast: pulls any scalar
    -- function `g` through the equivalence.
    have hy_reindex : ∀ g : ℝ → ℝ, (∑ j, g (y j)) = ∑ j : Fin q.n, g (q.atom j) := fun g => by
      dsimp [y]
      simpa using
        (Equiv.sum_comp ((Fin.castOrderIso hn).toEquiv) (fun j : Fin q.n => g (q.atom j)))
    have h_unweighted :
        ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ → ∑ i, φ (p.atom i) ≤ ∑ j, φ (y j) := by
      intro φ hφ
      rw [hy_reindex φ]
      exact convexOrder_unweighted_of_uniform hn_pos hn hp_uniform hq_uniform h φ hφ
    have h_sum_eq : ∑ i, p.atom i = ∑ j, y j := by
      rw [hy_reindex (fun x => x)]
      exact sum_eq_of_uniform_mean_eq hn_pos hn hp_uniform hq_uniform hmean_eq
    have h_core :
        ∃ D : Matrix (Fin p.n) (Fin p.n) ℝ,
          D ∈ doublyStochastic ℝ (Fin p.n) ∧
            Matrix.mulVec D y = p.atom :=
      exists_doublyStochastic_mulVec_of_convex_dominates p.atom y h_unweighted h_sum_eq
    rcases h_core with ⟨D, hD, hDmean⟩
    exact BistochasticMartingaleMatrix.nonempty_of_doublyStochastic hn hp_uniform hq_uniform
      D hD (by simpa [y] using hDmean)

namespace BistochasticMartingaleMatrix

variable {p q : DiscreteLaw}

/-- Collapsing a row of the joint masses: `∑ⱼ ofReal(pᵢ · Tᵢⱼ) = ofReal pᵢ`. For an active row this
is `row_sum`; for a zero-weight row both sides vanish. Used by the total-mass proof and the first
marginal. -/
private lemma row_ofReal_sum (M : BistochasticMartingaleMatrix p q) (i : Fin p.n) :
    ∑ j, ENNReal.ofReal (p.weight i * M.T i j) = ENNReal.ofReal (p.weight i) := by
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun j _ => mul_nonneg (p.weight_nonneg i) (M.nonneg i j))]
  congr 1
  by_cases hi : p.weight i = 0
  · rw [hi]; simp
  · rw [← Finset.mul_sum, M.row_sum i hi, mul_one]

/-- The joint law `π({(p.atom i, q.atom j)}) = p.weight i · T i j`, promoted to a
`ProbDist (ℝ × ℝ)`. -/
noncomputable def toProbDist (M : BistochasticMartingaleMatrix p q) :
    ProbDist (ℝ × ℝ) :=
  ⟨∑ i, ∑ j, ENNReal.ofReal (p.weight i * M.T i j) •
      Measure.dirac (p.atom i, q.atom j), by
      constructor
      -- Total mass: `∑ᵢⱼ pᵢ · Tᵢⱼ = ∑ᵢ pᵢ · (∑ⱼ Tᵢⱼ) = ∑ᵢ pᵢ · 1 = 1`.
      simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
        smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ,
        Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, mul_one]
      -- Pull `ENNReal.ofReal` out of each inner sum, then over the outer sum.
      simp_rw [row_ofReal_sum M]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => p.weight_nonneg i),
        p.weight_sum, ENNReal.ofReal_one]⟩

@[simp] lemma toProbDist_toMeasure (M : BistochasticMartingaleMatrix p q) :
    M.toProbDist.toMeasure
      = ∑ i, ∑ j, ENNReal.ofReal (p.weight i * M.T i j)
          • Measure.dirac (p.atom i, q.atom j) :=
  rfl

/-- The assembled coupling has `p.toProbDist` as first marginal, `q.toProbDist` as second marginal,
and satisfies the tested martingale identity. -/
lemma isMartingaleCoupling (M : BistochasticMartingaleMatrix p q) :
    IsMartingaleCoupling p.toProbDist q.toProbDist M.toProbDist := by
  -- Convenience: integration against the joint measure reduces to a finite double sum.
  have hnn : ∀ i j, 0 ≤ p.weight i * M.T i j := fun i j =>
    mul_nonneg (p.weight_nonneg i) (M.nonneg i j)
  -- Every strongly measurable `f` is integrable against the finitely-supported joint measure:
  -- each scaled Dirac is integrable and the measure is a finite sum of them.
  have h_integ : ∀ f : ℝ × ℝ → ℝ, StronglyMeasurable f →
      Integrable f M.toProbDist.toMeasure := by
    intro f hf
    rw [toProbDist_toMeasure]
    refine integrable_finset_sum_measure.mpr fun i _ => ?_
    refine integrable_finset_sum_measure.mpr fun j _ => ?_
    exact (integrable_dirac' hf (a := (p.atom i, q.atom j))
      ENNReal.coe_lt_top).smul_measure ENNReal.ofReal_ne_top
  -- The integral against the total measure is a double sum of pointwise values.
  have h_int : ∀ f : ℝ × ℝ → ℝ, StronglyMeasurable f →
      ∫ x, f x ∂M.toProbDist.toMeasure
        = ∑ i, ∑ j, p.weight i * M.T i j * f (p.atom i, q.atom j) := by
    intro f hf
    rw [toProbDist_toMeasure]
    -- Pull the outer `∑ i` out of the integral.
    rw [integral_finset_sum_measure (fun i _ => by
      refine integrable_finset_sum_measure.mpr (fun j _ => ?_)
      exact (integrable_dirac' hf (a := (p.atom i, q.atom j))
        ENNReal.coe_lt_top).smul_measure ENNReal.ofReal_ne_top)]
    refine Finset.sum_congr rfl fun i _ => ?_
    -- Pull the inner `∑ j` out of the integral.
    rw [integral_finset_sum_measure (fun j _ =>
      (integrable_dirac' hf (a := (p.atom i, q.atom j))
        ENNReal.coe_lt_top).smul_measure ENNReal.ofReal_ne_top)]
    refine Finset.sum_congr rfl fun j _ => ?_
    -- Reduce `∫ f ∂(c • δ_x) = c.toReal • f x`.
    rw [integral_smul_measure, integral_dirac' _ _ hf,
      ENNReal.toReal_ofReal (hnn i j), smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- fst_marginal: pushforward by `Prod.fst` equals `p.toProbDist`.
    apply ProbabilityMeasure.toMeasure_injective
    change (Measure.map Prod.fst M.toProbDist.toMeasure) = p.toProbDist.toMeasure
    rw [toProbDist_toMeasure, DiscreteLaw.toProbDist_toMeasure]
    -- Push `Prod.fst` through both sums and each `c • δ_{(xᵢ,yⱼ)} = c • δ_{xᵢ}`.
    rw [MeasureTheory.measure_map_finset_sum measurable_fst]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MeasureTheory.measure_map_finset_sum measurable_fst]
    -- Each summand: `Measure.map fst (c • δ_{(xᵢ,yⱼ)}) = c • δ_{xᵢ}`.
    simp_rw [Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_dirac' measurable_fst]
    -- Combine the inner sum: `∑ⱼ ofReal (pᵢ Tᵢⱼ) • δ_{xᵢ} = ofReal pᵢ • δ_{xᵢ}`.
    rw [← Finset.sum_smul]
    congr 1
    exact row_ofReal_sum M i
  · -- snd_marginal: pushforward by `Prod.snd` equals `q.toProbDist`.
    apply ProbabilityMeasure.toMeasure_injective
    change (Measure.map Prod.snd M.toProbDist.toMeasure) = q.toProbDist.toMeasure
    rw [toProbDist_toMeasure, DiscreteLaw.toProbDist_toMeasure]
    rw [MeasureTheory.measure_map_finset_sum measurable_snd]
    simp_rw [MeasureTheory.measure_map_finset_sum measurable_snd,
      Measure.map_smul _ measurable_snd.aemeasurable, Measure.map_dirac' measurable_snd]
    -- Swap sums to group by `j` first.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hnn i j), M.col_marginal j]
  · -- integrable_fst: finitely-supported measure.
    exact h_integ _ measurable_fst.stronglyMeasurable
  · -- integrable_snd: analogous.
    exact h_integ _ measurable_snd.stronglyMeasurable
  · -- martingale: expand on the discrete support, use row_sum and mean_eq.
    intro φ hφ _
    have hf : StronglyMeasurable (fun x : ℝ × ℝ => (x.2 - x.1) * φ x.1) :=
      (measurable_snd.sub measurable_fst).stronglyMeasurable.mul
        (hφ.stronglyMeasurable.comp_measurable measurable_fst)
    rw [h_int _ hf]
    -- ∑ᵢⱼ pᵢTᵢⱼ (yⱼ - xᵢ) φ(xᵢ) = ∑ᵢ pᵢ φ(xᵢ) (∑ⱼ Tᵢⱼ yⱼ - xᵢ ∑ⱼ Tᵢⱼ) = 0.
    have hi : ∀ i, ∑ j, p.weight i * M.T i j *
          ((q.atom j - p.atom i) * φ (p.atom i)) = 0 := by
      intro i
      have h_expand : ∀ j, p.weight i * M.T i j *
            ((q.atom j - p.atom i) * φ (p.atom i))
          = p.weight i * φ (p.atom i) *
            (M.T i j * q.atom j - p.atom i * M.T i j) := by
        intro j; ring
      simp_rw [h_expand]
      by_cases hi : p.weight i = 0
      · rw [hi]
        simp
      · rw [← Finset.mul_sum]
        have hS : ∑ j, (M.T i j * q.atom j - p.atom i * M.T i j) = 0 := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, M.mean_eq i hi,
            M.row_sum i hi, mul_one, sub_self]
        rw [hS, mul_zero]
    simp_rw [hi]
    exact Finset.sum_const_zero

end BistochasticMartingaleMatrix

/-- Discrete Strassen — uniform equal-cardinality case: Two finitely-supported laws with equal atom
count and uniform weights `1/n`, in convex order, admit an explicit martingale coupling.

This is the special case consumed by the continuous Strassen proof. The general statement for
arbitrary finite support and nonuniform weights is `DiscreteLaw.exists_martingaleCoupling`. -/
theorem DiscreteLaw.exists_martingaleCoupling_uniform (p q : DiscreteLaw)
    (hn_pos : 0 < p.n) (hn : p.n = q.n)
    (hp_uniform : ∀ i, p.weight i = (1 : ℝ) / p.n)
    (hq_uniform : ∀ j, q.weight j = (1 : ℝ) / q.n)
    (h : DiscreteLaw.ConvexOrder p q) :
    ∃ π : ProbDist (ℝ × ℝ), IsMartingaleCoupling p.toProbDist q.toProbDist π := by
  obtain ⟨M⟩ := discrete_martingale_matrix_exists_uniform p q hn_pos hn hp_uniform hq_uniform h
  exact ⟨M.toProbDist, M.isMartingaleCoupling⟩

end Econlib.Probability
