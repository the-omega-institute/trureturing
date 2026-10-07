/- GID: D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Walk/ChainWiring
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian matrix walk, filtration and stopped increments. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Walk.Chain
import D5.S3.Arith.Lattices.Klartag.Walk.ChainDrift
import D5.S3.Arith.Lattices.Klartag.Walk.ChainEllipsoid
import D5.S3.Arith.Lattices.Klartag.Walk.Increments

open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Walk.ChainWiring

open Matrix
open MeasureTheory
open Finset
open Module
open scoped RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments

variable {n : ℕ}

theorem cc_ne_zero (p : UT n) : cc p ≠ 0 := by
  rw [cc]
  split
  · norm_num
  · positivity

/-- **The constraint vector of a lattice point**: the coordinates of `x ⊗ x` in the model. -/
noncomputable def qUT (x : Fin n → ℝ) : EuclideanSpace ℝ (UT n) :=
  WithLp.toLp 2 fun p => x p.1.1 * x p.1.2 / cc p

@[simp] theorem qUT_apply (x : Fin n → ℝ) (p : UT n) :
    (qUT x) p = x p.1.1 * x p.1.2 / cc p := rfl

/-- `q x` really is `x ⊗ x`. -/
theorem symMat_qUT (x : Fin n → ℝ) (i j : Fin n) : symMat (qUT x) i j = x i * x j := by
  rw [symMat_apply, qUT_apply, mul_comm, div_mul_cancel₀ _ (cc_ne_zero _)]
  rcases le_total i j with h | h
  · rw [up_of_le h]
  · rw [up_comm, up_of_le h]; ring

/-- **`⟪A, q x⟫` is the quadratic form.**  So `Chain.kSet q W` is the set of matrices whose
ellipsoid `E_A = {v | ⟪A v, v⟫ < 1}` (Klartag eq. 9) misses the window, and `Chain.freeSub q C`
is his `F_A` (eq. 13). -/
theorem inner_qUT_eq_quad (A : EuclideanSpace ℝ (UT n)) (x : Fin n → ℝ) :
    ⟪A, qUT x⟫ = (symMat A *ᵥ x) ⬝ᵥ x := by
  rw [← sum_symMat_mul_eq_inner]
  simp only [symMat_qUT]
  rw [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Non-negative correlation** — hinge 1's `⟪x ⊗ x, y ⊗ y⟫ = (x ⬝ᵥ y)²`, the hypothesis
`Chain.lift_mem_kSet` runs on. -/
theorem inner_qUT (x y : Fin n → ℝ) : ⟪qUT x, qUT y⟫ = (x ⬝ᵥ y) ^ 2 := by
  rw [← sum_symMat_mul_eq_inner]
  simp only [symMat_qUT]
  rw [sq, dotProduct, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem inner_qUT_nonneg (x y : Fin n → ℝ) : (0 : ℝ) ≤ ⟪qUT x, qUT y⟫ := by
  rw [inner_qUT]; positivity

theorem card_UT (n : ℕ) : Fintype.card (UT n) = n * (n + 1) / 2 := by
  classical
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun a b : Fin n => a ≤ b),
    Fintype.card_sigma]
  have h1 : ∀ i : Fin n, Fintype.card {j : Fin n // i ≤ j} = n - (i : ℕ) := by
    intro i
    rw [Fintype.card_subtype]
    have hset : (Finset.univ.filter fun j : Fin n => i ≤ j) = Finset.Ici i := by
      ext j; simp
    rw [hset, Fin.card_Ici]
  simp_rw [h1]
  rw [Fin.sum_univ_eq_sum_range (fun i => n - i) n]
  have h2 : ∑ i ∈ Finset.range n, (n - i) = ∑ i ∈ Finset.range n, (i + 1) := by
    rw [← Finset.sum_range_reflect (fun i => i + 1) n]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    omega
  rw [h2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  set S := ∑ i ∈ Finset.range n, i with hS
  have h3 : S * 2 = n * (n - 1) := Finset.sum_range_id_mul_two n
  have h4 : (S + n) * 2 = n * (n + 1) := by
    rcases n with _ | m
    · simp [hS]
    · have : (m + 1) - 1 = m := by omega
      rw [this] at h3
      nlinarith [h3]
  omega

section Err

variable {ι : Type*} [DecidableEq ι] {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι}
  {A₀ : EuclideanSpace ℝ (UT n)} {Ω : Type*} {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- `log det` of a point of the model. -/
noncomputable def logDet (A : EuclideanSpace ℝ (UT n)) : ℝ := Real.log (symMat A).det

/-- **`err`**: the log-det cost of the correction at one step — the entire discretisation error
of the chain. -/
noncomputable def liftCost (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A' : EuclideanSpace ℝ (UT n)) : ℝ :=
  logDet (Chain.lift q W A') - logDet A'

/-- The chain's stepped matrix `A'_{k+1}` before the correction. -/
noncomputable def preState (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (k : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (UT n) :=
  (Chain.chain q W A₀ ξ k ω).1
    + (Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)

/-- **The chain's `err k`.** -/
noncomputable def chainErr (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (k : ℕ) (ω : Ω) : ℝ :=
  liftCost q W (preState q W A₀ ξ k ω)

/-- The step's log-determinant splits as the Gaussian part plus the error. -/
theorem logDet_chain_succ (k : ℕ) (ω : Ω) :
    logDet (Chain.chain q W A₀ ξ (k + 1) ω).1
      = logDet (preState q W A₀ ξ k ω) + chainErr q W A₀ ξ k ω := by
  simp only [chainErr, liftCost, preState, Chain.chain_succ, Chain.stepTo]
  ring

end Err

section Integrability

variable {ι : Type*} [DecidableEq ι] [Countable ι] {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι}
  {A₀ : EuclideanSpace ℝ (UT n)} {Ω : Type*} [MeasurableSpace Ω]
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {μ : Measure Ω}

/-- The active set is a measurable `Finset`-valued random variable, fibre by fibre. -/
theorem measurableSet_active_eq (hξ : ∀ k, Measurable (ξ k)) (k : ℕ) (c : Finset ι) :
    MeasurableSet {ω | (Chain.chain q W A₀ ξ k ω).2 = c} := by
  by_cases hc : c ⊆ W
  · have hset : {ω | (Chain.chain q W A₀ ξ k ω).2 = c}
        = (⋂ i ∈ (c : Set ι), {ω | i ∈ (Chain.chain q W A₀ ξ k ω).2})
          ∩ ⋂ i ∈ ((W \ c : Finset ι) : Set ι), {ω | i ∈ (Chain.chain q W A₀ ξ k ω).2}ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_coe,
        Finset.mem_sdiff, Set.mem_compl_iff]
      constructor
      · intro heq
        refine ⟨fun i hi => by rw [heq]; exact hi, fun i hi hmem => ?_⟩
        rw [heq] at hmem
        exact hi.2 hmem
      · rintro ⟨h1, h2⟩
        ext i
        constructor
        · intro hi
          by_contra hic
          exact h2 i ⟨Chain.chain_snd_subset_window k ω hi, hic⟩ hi
        · exact fun hi => h1 i hi
    rw [hset]
    exact MeasurableSet.inter
      (MeasurableSet.biInter (Finset.countable_toSet c)
        fun i _ => Chain.measurableSet_mem_active hξ k i)
      (MeasurableSet.biInter (Finset.countable_toSet (W \ c))
        fun i _ => (Chain.measurableSet_mem_active hξ k i).compl)
  · have hset : {ω | (Chain.chain q W A₀ ξ k ω).2 = c} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro heq
      exact hc (heq ▸ Chain.chain_snd_subset_window k ω)
    rw [hset]
    exact MeasurableSet.empty

/-- **Any real function of the active set is a measurable random variable.**  The active set takes
finitely many values (`Finset.powerset W`), so the composition is a finite sum of indicators. -/
theorem measurable_of_active (hξ : ∀ k, Measurable (ξ k)) (k : ℕ) (f : Finset ι → ℝ) :
    Measurable fun ω => f (Chain.chain q W A₀ ξ k ω).2 := by
  classical
  have hrep : (fun ω => f (Chain.chain q W A₀ ξ k ω).2)
      = fun ω => ∑ c ∈ W.powerset, if (Chain.chain q W A₀ ξ k ω).2 = c then f c else 0 := by
    funext ω
    rw [Finset.sum_ite_eq W.powerset (Chain.chain q W A₀ ξ k ω).2 f,
      if_pos (Finset.mem_powerset.2 (Chain.chain_snd_subset_window k ω))]
  rw [hrep]
  refine Finset.measurable_sum _ fun c _ => ?_
  exact Measurable.ite (measurableSet_active_eq hξ k c) measurable_const measurable_const

/-- `N_k = dim F(C_k)` is measurable. -/
theorem measurable_freeDim (hξ : ∀ k, Measurable (ξ k)) (k : ℕ) :
    Measurable fun ω => ((Chain.freeDim q W A₀ ξ k ω : ℕ) : ℝ) :=
  measurable_of_active hξ k fun c => (finrank ℝ (Chain.freeSub q c) : ℝ)

theorem integrable_of_ae_bound [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    {C : ℝ} (hb : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C) : Integrable f μ :=
  Integrable.mono' (integrable_const C) hf hb

/-- **`intD` from a two-sided bound on the determinant.**  The lower bound is Klartag eq. (32),
`det A_t ≥ c_L`, from Minkowski's first theorem (`det_ge_of_volume_le` below); the upper bound is
the good event of Corollary 3.2 (H5). -/
theorem integrable_logDet_of_bounds [IsFiniteMeasure μ] {D : Ω → ℝ}
    (hmeas : AEStronglyMeasurable D μ) {cL C : ℝ} (hcL : 0 < cL)
    (hb : ∀ᵐ ω ∂μ, cL ≤ Real.exp (D ω) ∧ Real.exp (D ω) ≤ C) : Integrable D μ := by
  refine integrable_of_ae_bound hmeas (C := |Real.log cL| + |Real.log C|) ?_
  filter_upwards [hb] with ω hω
  have h1 : Real.log cL ≤ D ω := by
    have := Real.log_le_log hcL hω.1
    rwa [Real.log_exp] at this
  have h2 : D ω ≤ Real.log C := by
    have := Real.log_le_log (lt_of_lt_of_le hcL hω.1) hω.2
    rwa [Real.log_exp] at this
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have := neg_abs_le (Real.log cL); have := abs_nonneg (Real.log C); linarith
  · have := le_abs_self (Real.log C); have := abs_nonneg (Real.log cL); linarith

end Integrability

section Minkowski

variable {n : ℕ}

/-- The quadratic form of a matrix, `Q_M(v) = ⟪M v, v⟫`. -/
noncomputable def quadForm (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ := (M *ᵥ v) ⬝ᵥ v

theorem quadForm_eq_inner (A : EuclideanSpace ℝ (UT n)) (x : Fin n → ℝ) :
    ⟪A, qUT x⟫ = quadForm (symMat A) x := inner_qUT_eq_quad A x

end Minkowski

section Overshoot

variable {ι : Type*} [DecidableEq ι] {W : Finset ι} {xs : ι → (Fin n → ℝ)}

omit [DecidableEq ι] in
theorem lift_sub (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A' : EuclideanSpace ℝ (UT n)) :
    Chain.lift q W A' - A'
      = ∑ i ∈ Chain.violated q W A', ((1 - ⟪A', q i⟫) / ‖q i‖ ^ 2) • q i := by
  rw [Chain.lift, add_sub_cancel_left]

omit [DecidableEq ι] in
/-- **The correction's cost carries no Frobenius norm.**  With `q i = x_i ⊗ x_i`,
`⟪B, Δ⟫ = ∑_i λ_i · ⟪B x_i, x_i⟫`, so the concavity bound on the log-determinant reads
`∑_i λ_i ⟪(A')⁻¹ x_i, x_i⟫ ≤ λ_min(A')⁻¹ ∑_i λ_i |x_i|²` — one factor of `√n` cheaper than
`‖(A')⁻¹‖_F · ‖Δ‖_F`, which is what the Frobenius projection would force. -/
theorem inner_lift_sub (B A' : EuclideanSpace ℝ (UT n)) :
    ⟪B, Chain.lift (fun i => qUT (xs i)) W A' - A'⟫
      = ∑ i ∈ Chain.violated (fun i => qUT (xs i)) W A',
          ((1 - ⟪A', qUT (xs i)⟫) / ‖qUT (xs i)‖ ^ 2) * quadForm (symMat B) (xs i) := by
  rw [lift_sub, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right, quadForm_eq_inner, quadForm_eq_inner]

/-- **Each coefficient is bounded by the step's own increment against that constraint.**  This is
what makes the overshoot `O(√h)` rather than `O(n√h)`: `1 - ⟪A + B, q i⟫ ≤ -⟪B, q i⟫` because
`A` already satisfies the constraint. -/
theorem coeff_le {q : ι → EuclideanSpace ℝ (UT n)} {A B : EuclideanSpace ℝ (UT n)}
    (hA : A ∈ Chain.kSet q W) {i : ι} (hi : i ∈ Chain.violated q W (A + B)) :
    (1 - ⟪A + B, q i⟫) / ‖q i‖ ^ 2 ≤ (-⟪B, q i⟫) / ‖q i‖ ^ 2 := by
  obtain ⟨hiW, _⟩ := Chain.mem_violated.1 hi
  have h1 : (1 : ℝ) ≤ ⟪A, q i⟫ := hA i hiW
  have h2 : ⟪A + B, q i⟫ = ⟪A, q i⟫ + ⟪B, q i⟫ := inner_add_left _ _ _
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
  rw [h2]
  linarith

end Overshoot

section Assembly

variable {ι : Type*} [DecidableEq ι] [Countable ι] {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι}
  {A₀ : EuclideanSpace ℝ (UT n)} {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {ℱ : ℕ → MeasurableSpace Ω}

end Assembly

end D5.S3.Arith.Lattices.Klartag.Walk.ChainWiring
