/- GID: D5/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Tail/TailAtStepR5W2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lattice tail bounds along the matrix walk. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Tail.TailAtStepR2W2
import D5.S3.Arith.Lattices.Klartag.Contact.Lemma43UniformR2
import D5.S3.Arith.Lattices.Klartag.Completion.TerminalCount
import D5.S3.Arith.Lattices.Klartag.Walk.ChainWalkRW2
import D5.S3.Arith.Lattices.Klartag.Contact.Lemma43UniformR3
import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped8R5
import D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup3W2
import D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped8
import Mathlib
import D5.S3.Arith.Lattices.Klartag.Completion.Theorem2
import D5.S3.Arith.Lattices.Klartag.Construction.LatticeData
import D5.S3.Arith.Lattices.Klartag.Construction.LatticeDataR
import D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup3
import D5.S3.Arith.Lattices.Klartag.Tail.TailAtStep
import D5.S3.Arith.Lattices.Klartag.Walk.ChainInputDom
import D5.S3.Arith.Lattices.Klartag.Completion.WindowR
import D5.S3.Arith.Lattices.Klartag.Contact.ThetaTight
import D5.S3.Arith.Lattices.Klartag.Completion.GoodPathLight

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Lemma43R
open D5.S3.Arith.Lattices.Klartag.Lemma43R2
open D5.S3.Arith.Lattices.Klartag.Lemma43R3
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Tail.TailAtStepR5W2

open MeasureTheory
open Set
open Real
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Completion.WindowR2
open D5.S3.Arith.Lattices.Klartag.Walk.Chain

noncomputable section

variable {n : ℕ}

/-- **The raw datum with a terminal weight.**  `ChainRaw2RW2` plus the single-time bound the
count event needs. -/
structure ChainRaw3 (p n : ℕ) extends ChainRaw2RW2 p n where
  /-- The terminal contact weight. -/
  wT : (Fin n → ℤ) → ℝ≥0∞

  tailT : ∀ y ∈ toChainRaw2RW2.supp, wT y ≤ ENNReal.ofReal
    (4 * profileAt (a0C n) toChainRaw2RW2.alpha
      (windowR2 toChainRaw2RW2.alpha n) n (ChainDrift.horizon n) ‖toE n y‖)

/-- The terminal step's bound is below the horizon's, by monotonicity of `profile` in `t`. -/
theorem profStep_le_horizon {α : ℝ} (hn : 3 ≤ n) {K : ℕ} (y : Fin n → ℤ)
    (hK : (K : ℝ) * ParamsAdopted2.stepSizeAdopted2 n ≤ ChainDrift.horizon n) :
    profStepRW2 α n (ParamsAdopted2.stepSizeAdopted2 n) y K
      ≤ profileAt (a0C n) α (windowR2 α n) n (ChainDrift.horizon n) ‖toE n y‖ := by
  by_cases h0 : K = 0
  · simp only [profStepRW2, if_pos h0]
    exact profile_nonneg _ _
  · simp only [profStepRW2, if_neg h0]
    have hKpos : (0 : ℝ) < (K : ℝ) * ParamsAdopted2.stepSizeAdopted2 n := by
      have h1 : (0 : ℝ) < (K : ℝ) := by
        have : 0 < K := Nat.pos_of_ne_zero h0
        exact_mod_cast this
      have h2 : 0 < ParamsAdopted2.stepSizeAdopted2 n :=
        TailSideSetup2.stepSizeAdopted2_pos hn
      positivity
    exact profile_mono_time hKpos hK _

/-- The `t`-integrated profile bound, **as** the weight.  `ChainRaw2RW2.tail` at it is `le_refl`. -/
def wProf (α : ℝ) (n : ℕ) : (Fin n → ℤ) → ℝ≥0∞ := fun y =>
  ENNReal.ofReal (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
    profileAt (a0C n) α (windowR2 α n) n t ‖toE n y‖)

/-- The terminal profile bound, **as** the weight.  `ChainRaw3.tailT` at it is `le_refl`. -/
def wProfT (α : ℝ) (n : ℕ) : (Fin n → ℤ) → ℝ≥0∞ := fun y =>
  ENNReal.ofReal (4 * profileAt (a0C n) α (windowR2 α n) n (ChainDrift.horizon n) ‖toE n y‖)

/-- **The weight swap (route note).**  Any `ChainRaw2RW2` becomes a `ChainRaw3` whose two weights
are the profile bounds themselves: every arithmetic field is carried over untouched and both tail
fields are `le_refl`, so the record is `g`-free and chain-free. -/
def chainRaw3_of_raw2 {p n : ℕ} (Q : ChainRaw2RW2 p n) : ChainRaw3 p n where
  toChainRaw2RW2 := { Q with w := wProf Q.alpha n, tail := fun _y _hy => le_refl _ }
  wT := wProfT Q.alpha n
  tailT := fun _y _hy => le_refl _

/-- **`Params.integrable` for a single-time profile.**  `integrable_radial_euclidean` without the
`t`-integral: bounded by `1/2`, supported in `closedBall 0 W`. -/
theorem integrable_profile_euclidean {a₀ α W T : ℝ} {n : ℕ} :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => profile a₀ α W n T ‖x‖) := by
  have hsm : StronglyMeasurable (fun x : EuclideanSpace ℝ (Fin n) => profile a₀ α W n T ‖x‖) :=
    (measurable_profile_radius (a₀ := a₀) (α := α) (W := W) (n := n)
      T).stronglyMeasurable.comp_measurable continuous_norm.measurable
  have h1 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) => profile a₀ α W n T ‖x‖)
      (Metric.closedBall 0 W) :=
    integrableOn_of_bounded' measurableSet_closedBall (measure_closedBall_lt_top).ne
      hsm.aestronglyMeasurable (M := 1 / 2) (fun x _ => norm_profile_le T ‖x‖)
  have h2 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) => profile a₀ α W n T ‖x‖)
      (Metric.closedBall 0 W)ᶜ := by
    refine (integrableOn_zero (μ := volume)
      (s := (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) W)ᶜ)).congr_fun ?_
      measurableSet_closedBall.compl
    intro x hx
    exact (profile_zero_of_gt
      (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx)).symm
  rw [← integrableOn_univ, ← union_compl_self (Metric.closedBall
    (0 : EuclideanSpace ℝ (Fin n)) W)]
  exact h1.union h2

/-- **`Params.dom` for a single-time profile.**  `dom_of_tail2` without the `t`-integral; the
shift in `profileAt` is again exactly the cube radius `√n/2`. -/
theorem dom_of_tailT {n : ℕ} (hn : 0 < n) {a₀ α W T c : ℝ} (hα : 0 < α) (hT : 0 < T) (hc : 0 ≤ c)
    (w : (Fin n → ℤ) → ℝ≥0∞) (supp : Finset (Fin n → ℤ))
    (htail : ∀ y ∈ supp, w y ≤ ENNReal.ofReal (c * profileAt a₀ α W n T ‖toE n y‖)) :
    ∀ y ∈ supp, ∀ x ∈ cube (toE n y),
      w y ≤ ENNReal.ofReal (c * profile a₀ α W n T ‖x‖) := by
  intro y hy x hx
  have hanti : Antitone (fun r : ℝ => c * profileAt a₀ α W n T r) :=
    fun _ _ h => mul_le_mul_of_nonneg_left (profileAt_antitone hα hT h) hc
  have hwide := dom_of_antitone hn hanti supp y hy x hx
  have heq : (c * profileAt a₀ α W n T (‖x‖ - Real.sqrt n / 2))
      = c * profile a₀ α W n T ‖x‖ := by
    simp [profileAt, sub_add_cancel]
  rw [heq] at hwide
  exact le_trans (htail y hy) hwide

/-- The combined contact weight: `A·w_int + B·w_T`, in `ℝ≥0∞`. -/
def combW {p n : ℕ} (A B : ℝ) (Q : ChainRaw3 p n) : (Fin n → ℤ) → ℝ≥0∞ :=
  fun y => ENNReal.ofReal A * Q.w y + ENNReal.ofReal B * Q.wT y

/-- Its radial profile.  The `4`s of `ChainRaw3.tail` and `ChainRaw3.tailT` sit inside, so the
second coefficient is `4·B`; that is the `b` of `Lemma43R3.radial_bound_combined_le`. -/
def combF (A B α : ℝ) (n : ℕ) : ℝ → ℝ := fun r =>
  A * (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
        profile (a0C n) α (windowR2 α n) n t r)
    + 4 * B * profile (a0C n) α (windowR2 α n) n (ChainDrift.horizon n) r

/-- Lemma 4.3's constant for `combF`: the two constants already proved, scaled and added.  **No new
factor of `n` enters** (kill rule 2) — this is 85e §3's right-hand side. -/
def C3 (n : ℕ) (A B α : ℝ) : ℝ :=
  A * (4 * Lemma43R.C1R α n * (8 - 8 / (n : ℝ) ^ 2))
    + 4 * B * (Lemma43R.C1cR (a0C n) α n * (n : ℝ) ^ 2)

theorem C3_pos {n : ℕ} {A B α : ℝ} (hn : 2073600 ≤ n) (hα : 0 < α) (hA : 0 < A) (hB : 0 ≤ B) :
    0 < C3 n A B α := by
  have h1 : 0 < 4 * Lemma43R.C1R α n * (8 - 8 / (n : ℝ) ^ 2) := Lemma43R.C4_pos hn hα
  have h2 : 0 ≤ Lemma43R.C1cR (a0C n) α n := Lemma43R.C1cR_nonneg hα
  have h3 : (0 : ℝ) ≤ 4 * B * (Lemma43R.C1cR (a0C n) α n * (n : ℝ) ^ 2) := by
    have : (0 : ℝ) ≤ Lemma43R.C1cR (a0C n) α n * (n : ℝ) ^ 2 := by positivity
    have h4B : (0 : ℝ) ≤ 4 * B := by linarith
    exact mul_nonneg h4B this
  have h4 : 0 < A * (4 * Lemma43R.C1R α n * (8 - 8 / (n : ℝ) ^ 2)) := mul_pos hA h1
  unfold C3
  linarith

/-- `combF` is nonnegative. -/
theorem combF_nonneg {A B α : ℝ} {n : ℕ} (hA : 0 ≤ A) (hB : 0 ≤ B) (r : ℝ) :
    0 ≤ combF A B α n r := by
  have hI : (0 : ℝ) ≤ ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
      profile (a0C n) α (windowR2 α n) n t r :=
    setIntegral_nonneg measurableSet_Ioc (fun t _ => profile_nonneg t r)
  have hP : (0 : ℝ) ≤ profile (a0C n) α (windowR2 α n) n (ChainDrift.horizon n) r :=
    profile_nonneg _ _
  have h1 : (0 : ℝ) ≤ A * (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
      profile (a0C n) α (windowR2 α n) n t r) := mul_nonneg hA (by linarith)
  have h2 : (0 : ℝ) ≤ 4 * B * profile (a0C n) α (windowR2 α n) n (ChainDrift.horizon n) r :=
    mul_nonneg (by linarith) hP
  unfold combF
  linarith

/-- The `ℝ≥0∞` arithmetic of `Params.dom` for a sum of two weights, isolated so the record below
does not carry it inline. -/
theorem ofReal_comb_le {A B u v : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hu : 0 ≤ u) (hv : 0 ≤ v)
    {a b : ℝ≥0∞} (ha : a ≤ ENNReal.ofReal (4 * u)) (hb : b ≤ ENNReal.ofReal (4 * v)) :
    ENNReal.ofReal A * a + ENNReal.ofReal B * b
      ≤ ENNReal.ofReal (A * (4 * u) + 4 * B * v) := by
  have h1 : ENNReal.ofReal A * a ≤ ENNReal.ofReal (A * (4 * u)) := by
    rw [ENNReal.ofReal_mul hA]; gcongr
  have h2 : ENNReal.ofReal B * b ≤ ENNReal.ofReal (4 * B * v) := by
    have he : (4 : ℝ) * B * v = B * (4 * v) := by ring
    rw [he, ENNReal.ofReal_mul hB]; gcongr
  have hu4 : (0 : ℝ) ≤ A * (4 * u) := mul_nonneg hA (by linarith)
  have hv4 : (0 : ℝ) ≤ 4 * B * v := mul_nonneg (by linarith) hv
  calc ENNReal.ofReal A * a + ENNReal.ofReal B * b
      ≤ ENNReal.ofReal (A * (4 * u)) + ENNReal.ofReal (4 * B * v) := add_le_add h1 h2
    _ = ENNReal.ofReal (A * (4 * u) + 4 * B * v) := (ENNReal.ofReal_add hu4 hv4).symm

def params_of_raw3 {p n : ℕ} [Fact (Nat.Prime p)] (hn : 2073600 ≤ n)
    (Q : ChainRaw3 p n) {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) : Params p n where
  dim_pos := by omega
  alpha := Q.alpha
  alpha_pos := Q.alpha_pos
  alpha_norm := Q.alpha_norm
  a0 := a0C n
  a0_eq := rfl
  R := Q.R
  R_nonneg := Q.R_nonneg
  R_scaled := Q.R_scaled
  R_lt_p := Q.R_lt_p
  tiling_defect := Q.tiling_defect
  T := ChainDrift.horizon n
  T_eq := rfl
  N := ChainDrift.numSteps n 5
  N_eq := rfl
  h := ChainDrift.stepSize n 5
  h_eq := rfl
  windowRadius := windowR2 Q.alpha n
  window_lt_p := Q.window_lt_p
  f := combF A B Q.alpha n
  f_nonneg := combF_nonneg hA.le hB
  w := combW A B Q
  supp := Q.supp
  supp_ne_zero := Q.supp_ne_zero
  supp_radius := Q.supp_radius
  dom := by
    intro y hy x hx
    have h1 := dom_of_tail2 (n := n) (by omega) Q.alpha_pos (by norm_num : (0 : ℝ) ≤ 4)
      Q.w Q.supp Q.tail y hy x hx
    have h2 := dom_of_tailT (n := n) (by omega) Q.alpha_pos (horizon_pos (by omega))
      (by norm_num : (0 : ℝ) ≤ 4) Q.wT Q.supp Q.tailT y hy x hx
    have hu : (0 : ℝ) ≤ ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
        profile (a0C n) Q.alpha (windowR2 Q.alpha n) n t ‖x‖ :=
      setIntegral_nonneg measurableSet_Ioc (fun t _ => profile_nonneg t _)
    have hv : (0 : ℝ) ≤ profile (a0C n) Q.alpha (windowR2 Q.alpha n) n
        (ChainDrift.horizon n) ‖x‖ := profile_nonneg _ _
    exact ofReal_comb_le hA.le hB hu hv h1 h2
  integrable := by
    have hI := integrable_radial_euclidean (a₀ := a0C n) (α := Q.alpha)
      (W := windowR2 Q.alpha n) (T := ChainDrift.horizon n) (n := n)
      (T_nonneg (by omega : 1 ≤ n))
    have hP := integrable_profile_euclidean (a₀ := a0C n) (α := Q.alpha)
      (W := windowR2 Q.alpha n) (T := ChainDrift.horizon n) (n := n)
    exact ((hI.const_mul 4).const_mul A).add (hP.const_mul (4 * B))
  C := C3 n A B Q.alpha
  radial_bound := by
    simpa only [combF, C3] using
      Lemma43R3.radial_bound_combined_le (α := Q.alpha) (a := A) (b := 4 * B) (n := n)
        hn Q.alpha_pos Q.tiling_defect hA.le (by linarith)
  theta := ENNReal.ofReal (ThetaTight.thetaTight p n (C3 n A B Q.alpha))
  theta_ne_zero := by
    have hC := C3_pos hn Q.alpha_pos hA hB
    have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.Prime.one_lt (Fact.out : Nat.Prime p))
    have hpn : (1 : ℝ) < (p : ℝ) ^ n := one_lt_pow₀ hpR (by omega)
    have hκ : 0 < kappa n := kappa_pos (by omega)
    have hnR : (0 : ℝ) < (n : ℝ) := by
      have : (0 : ℕ) < n := by omega
      exact_mod_cast this
    have hpos : 0 < ThetaTight.thetaTight p n (C3 n A B Q.alpha) := by
      rw [ThetaTight.thetaTight]
      exact div_pos (by positivity) (by linarith)
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  theta_ne_top := ENNReal.ofReal_ne_top
  markov :=
    TailAtStepR2W2.markov_tight (n := n) (p := p) (by omega)
      (Nat.Prime.one_lt (Fact.out : Nat.Prime p)) (C3_pos hn Q.alpha_pos hA hB)

/-- **`paramsProducer3`.**  `Theorem2R3.ParamsProducerR2`'s five equalities, with `ChainRaw3` in
the binder and the combined weight in the fourth — all five are `rfl` on the record above. -/
theorem paramsProducer3 {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) :
    ∀ (p m : ℕ) (_ : Fact (Nat.Prime p)), 2073600 ≤ m + 1 → ∀ Q : ChainRaw3 p (m + 1),
      ∃ P : Params p (m + 1), P.alpha = Q.alpha ∧ P.R = Q.R ∧ P.supp = Q.supp ∧
        P.w = combW A B Q ∧
        P.theta = ENNReal.ofReal (ThetaTight.thetaTight p (m + 1) (C3 (m + 1) A B Q.alpha)) := by
  intro p m _hp hm Q
  exact ⟨params_of_raw3 hm Q hA hB, rfl, rfl, rfl, rfl, rfl⟩

/-- **The split, at a general §5 threshold.**  `TerminalCount.sums_of_combined` asks for
`∑ < 1`; the §5 output is `∑ < θ`, so the coefficients passed to it are divided by `θ`, and the two
admissibility facts become `θ ≤ A·θ₁` and `θ ≤ B·θ₂`.  That pair is scale-invariant in `(A, B)`,
which is why no normalisation of the combined weight is needed. -/
theorem sums_split {ι : Type*} {S : Finset ι} {w₁ w₂ : ι → ℝ≥0∞} {A B : ℝ} {θ θ₁ θ₂ : ℝ≥0∞}
    (hθ0 : θ ≠ 0) (hθt : θ ≠ ⊤)
    (h : ∑ y ∈ S, (ENNReal.ofReal A * w₁ y + ENNReal.ofReal B * w₂ y) < θ)
    (h₁ : θ ≤ ENNReal.ofReal A * θ₁) (h₂ : θ ≤ ENNReal.ofReal B * θ₂) :
    (∑ y ∈ S, w₁ y) < θ₁ ∧ (∑ y ∈ S, w₂ y) < θ₂ := by
  have hinv0 : θ⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hθt
  have hinvt : θ⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hθ0
  have hcancel : θ⁻¹ * θ = 1 := ENNReal.inv_mul_cancel hθ0 hθt
  refine TerminalCount.sums_of_combined (c₁ := ENNReal.ofReal A * θ⁻¹)
    (c₂ := ENNReal.ofReal B * θ⁻¹) ?_ ?_ ?_
  · have hs : ∑ y ∈ S, (ENNReal.ofReal A * θ⁻¹ * w₁ y + ENNReal.ofReal B * θ⁻¹ * w₂ y)
        = θ⁻¹ * ∑ y ∈ S, (ENNReal.ofReal A * w₁ y + ENNReal.ofReal B * w₂ y) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    have hlt : (∑ y ∈ S, (ENNReal.ofReal A * w₁ y + ENNReal.ofReal B * w₂ y)) * θ⁻¹
        < θ * θ⁻¹ := ENNReal.mul_lt_mul_left hinv0 hinvt h
    rw [hs]
    calc θ⁻¹ * ∑ y ∈ S, (ENNReal.ofReal A * w₁ y + ENNReal.ofReal B * w₂ y)
        = (∑ y ∈ S, (ENNReal.ofReal A * w₁ y + ENNReal.ofReal B * w₂ y)) * θ⁻¹ := by ring
      _ < θ * θ⁻¹ := hlt
      _ = 1 := ENNReal.mul_inv_cancel hθ0 hθt
  · calc (1 : ℝ≥0∞) = θ⁻¹ * θ := hcancel.symm
      _ ≤ θ⁻¹ * (ENNReal.ofReal A * θ₁) := by gcongr
      _ = ENNReal.ofReal A * θ⁻¹ * θ₁ := by ring
  · calc (1 : ℝ≥0∞) = θ⁻¹ * θ := hcancel.symm
      _ ≤ θ⁻¹ * (ENNReal.ofReal B * θ₂) := by gcongr
      _ = ENNReal.ofReal B * θ⁻¹ * θ₂ := by ring

section Transfer

variable {Ωc : Type*} [MeasurableSpace Ωc] {P : Measure Ωc} [IsProbabilityMeasure P]
variable {Ec : Type*} [NormedAddCommGroup Ec] [InnerProductSpace ℝ Ec] [FiniteDimensional ℝ Ec]
variable {q : (Fin n → ℤ) → Ec} {W : Finset (Fin n → ℤ)} {A₀ : Ec} {ξ : ℕ → Ωc → Ec} {α : ℝ}

end Transfer

end

end D5.S3.Arith.Lattices.Klartag.Tail.TailAtStepR5W2
