/- GID: D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stopped log determinant drift and integrability estimates. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped5

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped6

open MeasureTheory
open Matrix
open Finset
open Module
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.StoppedChain
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped4
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped5
open scoped RealInnerProductSpace

section Det

variable {n : ℕ}

/-- **Every eigenvalue is at least the quadratic form's lower bound.**  The companion of
`GoodEvent.abs_eigenvalues_le_opNorm`, which the tree has and which supplies the upper bound; this
direction is stated nowhere. -/
theorem le_eigenvalues_of_lower {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) {m : ℝ}
    (hlb : ∀ x : EuclideanSpace ℝ (Fin n),
      m * ‖x‖ ^ 2 ≤ ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A x⟫) (i : Fin n) :
    m ≤ hA.eigenvalues i := by
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) A with hT
  set v : EuclideanSpace ℝ (Fin n) := hA.eigenvectorBasis i with hv
  have hv1 : ‖v‖ = 1 := hA.eigenvectorBasis.norm_eq_one i
  have hTv : T v = hA.eigenvalues i • v := by
    apply WithLp.ofLp_injective 2
    rw [hT, Matrix.ofLp_toEuclideanCLM]
    simpa using hA.mulVec_eigenvectorBasis i
  have h := hlb v
  rw [hTv, real_inner_smul_right, real_inner_self_eq_norm_sq, hv1] at h
  simpa using h

/-- **`StateBounds` is a two-sided determinant bound.**  `m ≤ λᵢ ≤ M` for every eigenvalue, so
`mⁿ ≤ det A ≤ Mⁿ`.  This is what makes `log det` of the stopped state a bounded function. -/
theorem det_bounds_of_stateBounds {A : Matrix (Fin n) (Fin n) ℝ} {m M : ℝ}
    (hSB : Discharge.StateBounds A m M) : m ^ n ≤ A.det ∧ A.det ≤ M ^ n := by
  have hH : A.IsHermitian := hSB.posDef.isHermitian
  have hlow : ∀ i, m ≤ hH.eigenvalues i := le_eigenvalues_of_lower hH hSB.lower
  have hup : ∀ i, hH.eigenvalues i ≤ M := by
    intro i
    have h1 := GoodEvent.abs_eigenvalues_le_opNorm hH i
    have h2 := hSB.upper
    have h3 := le_abs_self (hH.eigenvalues i)
    linarith
  have hdet : A.det = ∏ i, hH.eigenvalues i := by simpa using hH.det_eq_prod_eigenvalues
  have hm0 : (0 : ℝ) ≤ m := hSB.mpos.le
  constructor
  · have h : ∏ _i : Fin n, m ≤ ∏ i, hH.eigenvalues i :=
      Finset.prod_le_prod₀ (fun i _ => hm0) (fun i _ => hlow i)
    simpa [hdet] using h
  · have h : ∏ i, hH.eigenvalues i ≤ ∏ _i : Fin n, M :=
      Finset.prod_le_prod₀ (fun i _ => le_trans hm0 (hlow i)) (fun i _ => hup i)
    simpa [hdet] using h

/-- `symMat` is linear in the Frobenius coordinates and `det` is a polynomial, so the composite is
continuous — the route to measurability of `logDet`. -/
theorem continuous_symMat_det :
    Continuous fun x : EuclideanSpace ℝ (UT n) => (symMat x).det := by
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  simp only [symMat_apply]
  exact continuous_const.mul (PiLp.continuous_apply 2 (fun _ : UT n => ℝ) (up i j))

end Det

section Fields

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

theorem measurable_logDet_chain (hξ : ∀ j, Measurable (ξ j)) (j : ℕ) :
    Measurable fun ω => ChainWiring.logDet (Chain.chain q W A₀ ξ j ω).1 := by
  have h1 : Measurable fun ω => (symMat (Chain.chain q W A₀ ξ j ω).1).det :=
    (continuous_symMat_det (n := n)).measurable.comp (Chain.measurable_chain_fst hξ j)
  exact Real.measurable_log.comp h1

/-- **`stoppedLogDet` is measurable.**  `min k (τ − 1)` takes values in `{0, …, k}`, so the stopped
state is a finite sum of indicators of the fibres of a measurable `ℕ`-valued map. -/
theorem measurable_stoppedLogDet (hξ : ∀ j, Measurable (ξ j)) {η r₀ c₃ : ℝ} {N : ℕ}
    (hτ : Measurable (tau q W A₀ ξ η r₀ c₃ N)) (k : ℕ) :
    Measurable (stoppedLogDet q W A₀ ξ η r₀ c₃ N k) := by
  classical
  have hmin : Measurable fun ω => min k (tau q W A₀ ξ η r₀ c₃ N ω - 1) :=
    measurable_const.min (hτ.sub_const 1)
  have hrep : stoppedLogDet q W A₀ ξ η r₀ c₃ N k
      = fun ω => ∑ j ∈ Finset.range (k + 1),
          if min k (tau q W A₀ ξ η r₀ c₃ N ω - 1) = j
            then ChainWiring.logDet (Chain.chain q W A₀ ξ j ω).1 else 0 := by
    funext ω
    rw [Finset.sum_ite_eq (Finset.range (k + 1)) (min k (tau q W A₀ ξ η r₀ c₃ N ω - 1))
      (fun j => ChainWiring.logDet (Chain.chain q W A₀ ξ j ω).1),
      if_pos (Finset.mem_range.2 (by omega))]
    rfl
  rw [hrep]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact Measurable.ite (hmin (measurableSet_singleton j)) (measurable_logDet_chain hξ j)
    measurable_const

/-- **`intD`, the drift's first integrability field.**  `stateBounds_stopped` holds for every `k`
and every `ω`, so the stopped log-determinant is bounded between `n·log m` and `n·log M`. -/
theorem integrable_stoppedLogDet {P : Measure Ω} [IsFiniteMeasure P]
    {η a₀ r₀ c₃ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hξ : ∀ j, Measurable (ξ j)) (hτ : Measurable (tau q W A₀ ξ η r₀ c₃ N))
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀) (k : ℕ) :
    Integrable (stoppedLogDet q W A₀ ξ η r₀ c₃ N k) P := by
  have hmpos : (0 : ℝ) < a₀ - (r₀ + c₃ * η) := by linarith
  refine ChainWiring.integrable_logDet_of_bounds
    (measurable_stoppedLogDet hξ hτ k).aestronglyMeasurable
    (cL := (a₀ - (r₀ + c₃ * η)) ^ n) (C := (a₀ + (r₀ + c₃ * η)) ^ n) (pow_pos hmpos n)
    (Filter.Eventually.of_forall fun ω => ?_)
  have hSB := stateBounds_stopped (ξ := ξ) (N := N) hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k ω
  obtain ⟨h1, h2⟩ := det_bounds_of_stateBounds hSB
  have hpos : 0 < (symMat (stoppedState q W A₀ ξ η r₀ c₃ N k ω)).det := hSB.posDef.det_pos
  have hexp : Real.exp (stoppedLogDet q W A₀ ξ η r₀ c₃ N k ω)
      = (symMat (stoppedState q W A₀ ξ η r₀ c₃ N k ω)).det := by
    rw [stoppedLogDet, ChainWiring.logDet, Real.exp_log hpos]
  rw [hexp]
  exact ⟨h1, h2⟩

noncomputable def stoppedFreeDim (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (η r₀ c₃ : ℝ)
    (N k : ℕ) (ω : Ω) : ℝ :=
  (finrank ℝ (stoppedSub q W A₀ ξ η r₀ c₃ N k ω) : ℝ)

omit [Countable ι] m0 in
theorem stoppedFreeDim_eq {η r₀ c₃ : ℝ} {N k : ℕ} (ω : Ω) :
    stoppedFreeDim q W A₀ ξ η r₀ c₃ N k ω
      = if k < tau q W A₀ ξ η r₀ c₃ N ω then ((Chain.freeDim q W A₀ ξ k ω : ℕ) : ℝ) else 0 := by
  rw [stoppedFreeDim, stoppedSub]
  by_cases h : k < tau q W A₀ ξ η r₀ c₃ N ω
  · rw [if_pos h, if_pos h, Chain.freeDim]
  · rw [if_neg h, if_neg h]
    simp

theorem measurable_stoppedFreeDim (hξ : ∀ j, Measurable (ξ j)) {η r₀ c₃ : ℝ} {N : ℕ}
    (hτ : Measurable (tau q W A₀ ξ η r₀ c₃ N)) (k : ℕ) :
    Measurable (stoppedFreeDim q W A₀ ξ η r₀ c₃ N k) := by
  have hrep : stoppedFreeDim q W A₀ ξ η r₀ c₃ N k
      = fun ω => if k < tau q W A₀ ξ η r₀ c₃ N ω
          then ((Chain.freeDim q W A₀ ξ k ω : ℕ) : ℝ) else 0 :=
    funext fun ω => stoppedFreeDim_eq ω
  rw [hrep]
  have hset : MeasurableSet {ω | k < tau q W A₀ ξ η r₀ c₃ N ω} := hτ trivial
  exact Measurable.ite hset (ChainWiring.measurable_freeDim hξ k) measurable_const

/-- **`intN`, the drift's second integrability field** — free, as it is for the unstopped chain
(`ChainWiring.integrable_freeDim`): the free dimension never exceeds `dim E`. -/
theorem integrable_stoppedFreeDim {P : Measure Ω} [IsFiniteMeasure P]
    (hξ : ∀ j, Measurable (ξ j)) {η r₀ c₃ : ℝ} {N : ℕ}
    (hτ : Measurable (tau q W A₀ ξ η r₀ c₃ N)) (k : ℕ) :
    Integrable (stoppedFreeDim q W A₀ ξ η r₀ c₃ N k) P := by
  refine ChainWiring.integrable_of_ae_bound
    (measurable_stoppedFreeDim hξ hτ k).aestronglyMeasurable
    (C := (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)) (Filter.Eventually.of_forall fun ω => ?_)
  rw [stoppedFreeDim, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact_mod_cast Submodule.finrank_le _

end Fields

section Integral

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}
variable {P : Measure Ω} [IsProbabilityMeasure P]

theorem integral_affine {C C₁ : ℝ} {g : Ω → ℝ} (hg : Integrable g P) :
    ∫ ω, (C + C₁ * g ω) ∂P = C + C₁ * ∫ ω, g ω ∂P := by
  rw [integral_add (integrable_const _) (hg.const_mul _), integral_const, integral_const_mul]
  simp

end Integral

section Drift

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}
variable {P : Measure Ω} [IsProbabilityMeasure P]

theorem logdet_bound_sum' {ℱ : ℕ → MeasurableSpace Ω} {D Nf err : ℕ → Ω → ℝ} {κ : ℝ} {m : ℕ}
    (h : ChainDrift.DriftInputs P ℱ D Nf err κ m) (hκ : 0 ≤ κ) {S E : ℝ}
    (hS : S ≤ ∑ k ∈ Finset.range m, ∫ ω, Nf k ω ∂P)
    (herr : ∑ k ∈ Finset.range m, ∫ ω, err k ω ∂P ≤ E) :
    ∫ ω, D m ω ∂P ≤ ∫ ω, D 0 ω ∂P - κ * S + E := by
  have hmain := ChainDrift.drift_bound h
  have hdrift : κ * S ≤ ∑ k ∈ Finset.range m, κ * ∫ ω, Nf k ω ∂P := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hS hκ
  linarith

omit [Countable ι] in

theorem drift_bound_stopped {ℱ : Filtration ℕ m0} {η r₀ c₃ c κ : ℝ} {N m : ℕ} {S E : ℝ}
    (hin : ChainDrift.DriftInputs P ⇑ℱ (stoppedLogDet q W A₀ ξ η r₀ c₃ N)
      (stoppedFreeDim q W A₀ ξ η r₀ c₃ N) (errCond P ⇑ℱ q W A₀ ξ η r₀ c₃ c N) κ m)
    (hκ : 0 ≤ κ)
    (hS : S ≤ ∑ k ∈ Finset.range m, ∫ ω, stoppedFreeDim q W A₀ ξ η r₀ c₃ N k ω ∂P)
    (herr : ∑ k ∈ Finset.range m, ∫ ω, stoppedErr q W A₀ ξ η r₀ c₃ c N k ω ∂P ≤ E) :
    ∫ ω, stoppedLogDet q W A₀ ξ η r₀ c₃ N m ω ∂P
      ≤ ∫ ω, stoppedLogDet q W A₀ ξ η r₀ c₃ N 0 ω ∂P - κ * S + E := by
  refine logdet_bound_sum' hin hκ hS ?_
  have hswap : ∀ k ∈ Finset.range m,
      ∫ ω, errCond P (⇑ℱ) q W A₀ ξ η r₀ c₃ c N k ω ∂P
        = ∫ ω, stoppedErr q W A₀ ξ η r₀ c₃ c N k ω ∂P := fun k _ => integral_errCond (hin.le k)
  rw [Finset.sum_congr rfl hswap]
  exact herr

end Drift

section Existence

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}
variable {P : Measure Ω} [IsProbabilityMeasure P]

end Existence

section Adopted

/-- `r₀` at the adopted parameters: the good event's operator-norm threshold `6√(T·n)`, which
`GoodEvent.lean:320` evaluates to `24√(log n / n)`. -/
noncomputable def r0Adopted (n : ℕ) : ℝ := 24 * Real.sqrt (Real.log n / (n : ℝ))

/-- `η` at the adopted parameters: `√(2 h d n)` with `h = ParamsAdopted2.stepSizeAdopted2 n`;
`ParamsAdopted2.eta2_le` bounds it by `√2 · n⁻³`. -/
noncomputable def etaAdopted (n : ℕ) : ℝ :=
  Real.sqrt (2 * ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ))

noncomputable def c3Adopted (n : ℕ) : ℝ := (n : ℝ) ^ 2

/-- **`m_adopted`**: the state's lower bound `a₀ − (r₀ + c₃η)`, `SlackHyp`'s first free argument.
`a₀ = (1 − 1/n)⁻²` is `D5.S3.Arith.Lattices.Klartag.a0C` (`Lemma43Uniform.lean:431`). -/
noncomputable def mAdopted (n : ℕ) : ℝ :=
  a0C n - (r0Adopted n + c3Adopted n * etaAdopted n)

/-- The state's upper bound `M = a₀ + (r₀ + c₃η)`. -/
noncomputable def MAdopted (n : ℕ) : ℝ :=
  a0C n + (r0Adopted n + c3Adopted n * etaAdopted n)

/-- `δ = η / m`, the smallest value `DriftStopped.hpt_stopped`'s `hδ` admits. -/
noncomputable def deltaAdopted (n : ℕ) : ℝ := etaAdopted n / mAdopted n

/-- **`c_adopted`**: the drift's quadratic coefficient `1 / (2 M² (1+δ)²)`, `SlackHyp`'s second
free argument — the `c` at which `DriftStopped.hpt_stopped` is stated. -/
noncomputable def cAdopted (n : ℕ) : ℝ :=
  1 / (2 * MAdopted n ^ 2 * (1 + deltaAdopted n) ^ 2)

/-- **`slack_adopted`**: the slack the middle case must fit into, of order `1`. -/
noncomputable def slackAdopted : ℝ := 1

end Adopted

end D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped6
