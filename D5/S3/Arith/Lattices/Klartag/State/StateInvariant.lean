/- GID: D5/S3/Arith/Lattices/Klartag/State/StateInvariant
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/State/StateInvariant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric matrix state invariants and padded driving laws. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.Discharge
import D5.S3.Arith.Lattices.Klartag.State.StepGlue

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.State.StateInvariant

open MeasureTheory
open Matrix
open Finset
open Module
open ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace MatrixOrder
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments

noncomputable section

section Bounds

variable {n : ℕ}

theorem symMat_add (x y : EuclideanSpace ℝ (UT n)) :
    symMat (x + y) = symMat x + symMat y := by
  ext i j; simp [symMat_apply]; ring

theorem symMat_zero : symMat (0 : EuclideanSpace ℝ (UT n)) = 0 := by
  ext i j; simp [symMat_apply]

theorem exists_congr_of_posDef {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∃ S : Matrix (Fin n) (Fin n) ℝ, S.IsHermitian ∧ S * A * S = 1 := by
  have hA0 : (0 : Matrix (Fin n) (Fin n) ℝ) ≤ A := hA.posSemidef.nonneg
  set R := CFC.sqrt A with hR
  have hRR : R * R = A := CFC.sqrt_mul_sqrt_self A hA0
  have hRpsd : R.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hdetA : IsUnit A.det := (ne_of_gt hA.det_pos).isUnit
  have hdetR : IsUnit R.det := by
    have h : R.det * R.det = A.det := by rw [← Matrix.det_mul, hRR]
    exact isUnit_of_mul_isUnit_left (by rw [h]; exact hdetA)
  refine ⟨R⁻¹, hRpsd.isHermitian.inv, ?_⟩
  calc R⁻¹ * A * R⁻¹ = (R⁻¹ * R) * (R * R⁻¹) := by rw [← hRR]; simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [Matrix.nonsing_inv_mul R hdetR, Matrix.mul_nonsing_inv R hdetR, Matrix.one_mul]

theorem stateBounds_of_opNorm_le {A : Matrix (Fin n) (Fin n) ℝ} {a₀ ρ : ℝ}
    (hA : A.IsSymm) (hρ0 : 0 ≤ ρ) (hlt : ρ < a₀)
    (hG : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A - a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))‖ ≤ ρ) :
    Discharge.StateBounds A (a₀ - ρ) (a₀ + ρ) := by
  have ha₀ : 0 < a₀ := lt_of_le_of_lt hρ0 hlt
  have hsplit : a₀ • (1 : Matrix (Fin n) (Fin n) ℝ)
      + (A - a₀ • (1 : Matrix (Fin n) (Fin n) ℝ)) = A := by abel
  have hlower : ∀ x : EuclideanSpace ℝ (Fin n),
      (a₀ - ρ) * ‖x‖ ^ 2 ≤ ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A x⟫ := by
    intro x
    have h := GoodEvent.lowerBound_of_opNorm_le (a₀ := a₀) hG x
    rwa [hsplit] at h
  have hmpos : 0 < a₀ - ρ := by linarith
  have hpd : A.PosDef := by
    refine GoodEvent.posDef_of_inner_pos (Matrix.isHermitian_iff_isSymm.2 hA) fun x hx => ?_
    have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hl := hlower x
    linarith [hl, mul_pos hmpos (pow_pos hx0 2)]
  refine ⟨hpd, hmpos, hlower, by linarith, ?_, exists_congr_of_posDef hpd⟩
  have hid : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))‖ ≤ a₀ := by
    rw [map_smul, map_one, norm_smul, Real.norm_eq_abs, abs_of_pos ha₀]
    calc a₀ * ‖(1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖
        ≤ a₀ * 1 := by
          exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le ha₀.le
      _ = a₀ := mul_one a₀
  calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖
      = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (A - a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))‖ := by
        rw [← map_add, hsplit]
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))‖
          + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A - a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))‖ :=
        norm_add_le _ _
    _ ≤ a₀ + ρ := add_le_add hid hG

end Bounds

section Decomposition

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*}
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- The projected Gaussian part of one step. -/
noncomputable def gaussStep (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (k : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (UT n) :=
  (Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)

/-- The one-sided lift applied at one step. -/
noncomputable def liftStep (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (k : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (UT n) :=
  (Chain.chain q W A₀ ξ (k + 1) ω).1 - ChainWiring.preState q W A₀ ξ k ω

noncomputable def gaussSum (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (k : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (UT n) :=
  ∑ j ∈ Finset.range k, gaussStep q W A₀ ξ j ω

noncomputable def liftSum (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (k : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (UT n) :=
  ∑ j ∈ Finset.range k, liftStep q W A₀ ξ j ω

theorem preState_eq (k : ℕ) (ω : Ω) :
    ChainWiring.preState q W A₀ ξ k ω
      = (Chain.chain q W A₀ ξ k ω).1 + gaussStep q W A₀ ξ k ω := rfl

/-- **The decomposition.**  `A_k = A₀ + (accumulated projected Gaussian) + (accumulated lifts)`. -/
theorem chain_fst_eq (k : ℕ) (ω : Ω) :
    (Chain.chain q W A₀ ξ k ω).1
      = A₀ + gaussSum q W A₀ ξ k ω + liftSum q W A₀ ξ k ω := by
  induction k with
  | zero => simp [gaussSum, liftSum]
  | succ k ih =>
    have h : (Chain.chain q W A₀ ξ (k + 1) ω).1
        = ChainWiring.preState q W A₀ ξ k ω + liftStep q W A₀ ξ k ω := by
      rw [liftStep]; abel
    rw [h, preState_eq, ih]
    simp only [gaussSum, liftSum, Finset.sum_range_succ]
    abel

end Decomposition

section Maurey

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `N(0, c²·Id)` on `E`: the standard Gaussian scaled by `c`. -/
def scaled (c : ℝ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure E :=
  (stdGaussian E).map (c • ·)

instance (c : ℝ) : IsProbabilityMeasure (scaled c E) := by
  unfold scaled
  exact inferInstance

theorem charFun_scaled (c : ℝ) (t : E) :
    charFun (scaled c E) t = Complex.exp (-(c ^ 2 * ‖t‖ ^ 2) / 2) := by
  rw [scaled, charFun_map_smul, charFun_stdGaussian]
  congr 1
  have h : ‖c • t‖ ^ 2 = c ^ 2 * ‖t‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hc : ((‖c • t‖ : ℝ) : ℂ) ^ 2 = ((c ^ 2 * ‖t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, h]
  rw [hc]
  push_cast
  ring

/-- **The convolution identity**: `N(0,a²) ∗ N(0,b²) = N(0,a²+b²)` on `E`. -/
theorem scaled_conv_scaled {a b : ℝ} (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    (scaled a E) ∗ (scaled b E) = scaled (Real.sqrt (a ^ 2 + b ^ 2)) E := by
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_conv, charFun_scaled, charFun_scaled, charFun_scaled, ← Complex.exp_add]
  congr 1
  have h : (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 = a ^ 2 + b ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hc : ((Real.sqrt (a ^ 2 + b ^ 2) : ℝ) : ℂ) ^ 2 = ((a ^ 2 + b ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, h]
  rw [hc]
  push_cast
  ring

end Maurey

section MaureyInd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem map_sum_scaled {X : ℕ → Ω → E} {c : ℝ} (hc : 0 ≤ c)
    (hmeas : ∀ j, Measurable (X j))
    (hlaw : ∀ j, P.map (X j) = scaled c E)
    (hind : ∀ k, IndepFun (fun ω => ∑ j ∈ Finset.range k, X j ω) (X k) P) (k : ℕ) :
    P.map (fun ω => ∑ j ∈ Finset.range k, X j ω) = scaled (Real.sqrt k * c) E := by
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, Real.sqrt_zero, zero_mul]
    rw [Measure.map_const]
    simp [scaled, Measure.map_const]
  | succ k ih =>
    have hSm : Measurable fun ω => ∑ j ∈ Finset.range k, X j ω :=
      Finset.measurable_sum _ fun j _ => hmeas j
    have hsplit : (fun ω => ∑ j ∈ Finset.range (k + 1), X j ω)
        = (fun ω => ∑ j ∈ Finset.range k, X j ω) + X k := by
      funext ω; simp [Finset.sum_range_succ]
    rw [hsplit, (hind k).map_add_eq_map_conv_map₀ hSm.aemeasurable (hmeas k).aemeasurable,
      ih, hlaw k, scaled_conv_scaled (by positivity) hc]
    congr 1
    have h : (Real.sqrt k * c) ^ 2 + c ^ 2 = ((k : ℝ) + 1) * c ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
      ring
    rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq hc]
    push_cast
    ring

end MaureyInd

section Split

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `π x + π x = x + R x` with `R = Submodule.reflection K`: the Maurey split at one step. -/
theorem starProjection_add_self (K : Submodule ℝ E) [K.HasOrthogonalProjection] (x : E) :
    K.starProjection x + K.starProjection x = x + K.reflection x := by
  rw [Submodule.reflection_apply, two_smul]
  abel

end Split

section SplitChain

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*}
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- The reflected increment `R_j ξ_j`, `R_j = π_j − π̃_j`. -/
noncomputable def reflStep (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (k : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (UT n) :=
  (Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).reflection (ξ k ω)

/-- **The Maurey split, accumulated**: `2 Σ_{j<k} π_j ξ_j = Σ_{j<k} ξ_j + Σ_{j<k} R_j ξ_j`.
Both sums on the right are over *unprojected* increments, which is what makes the induction
possible. -/
theorem gaussSum_add_self (k : ℕ) (ω : Ω) :
    gaussSum q W A₀ ξ k ω + gaussSum q W A₀ ξ k ω
      = (∑ j ∈ Finset.range k, ξ j ω) + ∑ j ∈ Finset.range k, reflStep q W A₀ ξ j ω := by
  rw [gaussSum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => starProjection_add_self _ _

/-- Hence the accumulated projected sum is dominated by the two halves. -/
theorem opNorm_gaussSum_le (k : ℕ) (ω : Ω) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (gaussSum q W A₀ ξ k ω))‖
      ≤ (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (∑ j ∈ Finset.range k, ξ j ω))‖
          + ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
              (symMat (∑ j ∈ Finset.range k, reflStep q W A₀ ξ j ω))‖) / 2 := by
  have h := gaussSum_add_self (q := q) (W := W) (A₀ := A₀) (ξ := ξ) k ω
  have h2 : Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (gaussSum q W A₀ ξ k ω))
      + Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (gaussSum q W A₀ ξ k ω))
      = Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (∑ j ∈ Finset.range k, ξ j ω))
        + Matrix.toEuclideanCLM (𝕜 := ℝ)
            (symMat (∑ j ∈ Finset.range k, reflStep q W A₀ ξ j ω)) := by
    rw [← map_add, ← map_add, ← symMat_add, ← symMat_add, h]
  have h3 := norm_add_le
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (∑ j ∈ Finset.range k, ξ j ω)))
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (∑ j ∈ Finset.range k, reflStep q W A₀ ξ j ω)))
  have h4 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (gaussSum q W A₀ ξ k ω))
      + Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (gaussSum q W A₀ ξ k ω))‖
      = 2 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (gaussSum q W A₀ ξ k ω))‖ := by
    rw [← two_smul ℝ, norm_smul, Real.norm_eq_abs]
    norm_num
  rw [h2] at h4
  linarith

end SplitChain

section Tail

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem symMat_smul (c : ℝ) (x : EuclideanSpace ℝ (UT n)) :
    symMat (c • x) = c • symMat x := by
  ext i j
  simp only [symMat_apply, Matrix.smul_apply, smul_eq_mul, PiLp.smul_apply]
  ring

theorem measurable_opNorm_symMat :
    Measurable fun x : EuclideanSpace ℝ (UT n) =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat x)‖ := by
  have h : ∀ x : EuclideanSpace ℝ (UT n), symMat x = mkMat (coordVec 1 x) := by
    intro x
    rw [← smul_symMat_eq_mkMat, one_smul]
  simp only [h]
  exact measurable_opNorm_mkMat.comp (measurable_coordVec 1)

omit [IsProbabilityMeasure P] in
/-- **Corollary 3.2 for a scaled standard Gaussian on the `UT n` carrier.**  If `Z` has law
`N(0, ρ²·Id)` then its symmetric matrix obeys Klartag's operator-norm tail. -/
theorem measureReal_opNorm_symMat_ge {Z : Ω → EuclideanSpace ℝ (UT n)} {ρ : ℝ} (hρ : 0 < ρ)
    (hZ : Measurable Z) (hlaw : P.map Z = scaled ρ (EuclideanSpace ℝ (UT n)))
    (s : ℝ) (hs : 1 ≤ s) :
    P.real {ω | 6 * ρ * s * Real.sqrt n ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (Z ω))‖}
      ≤ 4 * Real.exp (-(s ^ 2 * n)) := by
  set thr : ℝ := 6 * ρ * s * Real.sqrt n with hthr
  set S : Set (EuclideanSpace ℝ (UT n)) :=
    {z | thr ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat z)‖} with hS
  have hSmeas : MeasurableSet S :=
    measurableSet_le measurable_const measurable_opNorm_symMat
  rw [show {ω | thr ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (Z ω))‖} = Z ⁻¹' S from rfl,
    measureReal_preimage P hZ hSmeas, hlaw, scaled,
    ← measureReal_preimage (stdGaussian (EuclideanSpace ℝ (UT n)))
      (by fun_prop : Measurable fun x : EuclideanSpace ℝ (UT n) => ρ • x) hSmeas]
  have hset : (fun x : EuclideanSpace ℝ (UT n) => ρ • x) ⁻¹' S
      = {x : EuclideanSpace ℝ (UT n) | thr ≤
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (ρ • symMat x)‖} := by
    ext x
    simp only [Set.mem_preimage, hS, Set.mem_ofPred_eq, symMat_smul]
  rw [hset]
  exact increment_opNorm_tail hρ measurable_id (Measure.map_id) s hs

end Tail

section AccGood

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

def accGood (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι) (A₀ : EuclideanSpace ℝ (UT n))
    (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (N : ℕ) (r₀ : ℝ) : Set Ω :=
  {ω | ∀ k, k < N →
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (gaussSum q W A₀ ξ k ω))‖ ≤ r₀}

end AccGood

section Invariant

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

end Invariant

end

end D5.S3.Arith.Lattices.Klartag.State.StateInvariant
