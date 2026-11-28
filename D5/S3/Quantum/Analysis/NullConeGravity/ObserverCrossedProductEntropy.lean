/- GID: D5/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/ObserverCrossedProductEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite Gibbs clock corner has normalized trace and exact entropy identities. -/

import D5.S3.MeasureTheory.MatrixFieldEntropy
import D5.S3.Matrix.BlockEntropyIntegral
import D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
import D5.S3.Quantum.Lieb.PositiveMapJensen
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.Analysis.TraceClass.FiniteEntropyRelativeEntropy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! Weighted matrix fields and trace entropy for a positive Gibbs clock. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Analysis.NullConeGravity.ObserverCrossedProductEntropy

open MeasureTheory Set Matrix Omega.Matrix.BlockEntropy Omega.MeasureTheory.BoundedRing
open Omega.MeasureTheory.ExponentialClock
open Omega.MeasureTheory.MatrixFieldEntropy (weightedTrace weight)
open scoped Omega.MeasureTheory.BoundedRing
open scoped ENNReal BigOperators ComplexOrder CStarAlgebra MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Measurable matrix fields in total energy, modulo Lebesgue almost everywhere equality. -/
abbrev MatrixField (n : Type*) := ℝ →ₘ[volume] Matrix n n ℂ

/-- The bounded part of the total-energy field algebra. -/
def CoreField (n : Type*) [Fintype n] [DecidableEq n] : Subring (MatrixField n) :=
  boundedSubring

/-- The total-energy matrix of the cutoff on physical clock energy. -/
def activeProjection (E : n → ℝ) (y : ℝ) : Matrix n n ℂ :=
  diagonal fun i => if E i ≤ y then 1 else 0

omit [Fintype n] in
private theorem measurable_activeProjection (E : n → ℝ) : Measurable (activeProjection E) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  by_cases hij : i = j
  · subst j
    simp only [activeProjection, diagonal_apply_eq]
    exact measurable_const.piecewise measurableSet_Ici measurable_const
  · simp [activeProjection, diagonal_apply_ne _ hij]

private theorem activeProjection_sq (E : n → ℝ) (y : ℝ) :
    activeProjection E y * activeProjection E y = activeProjection E y := by
  rw [activeProjection, diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : E i ≤ y <;> simp [h]

omit [Fintype n] in
private theorem activeProjection_pos (E : n → ℝ) (y : ℝ) :
    (activeProjection E y).PosSemidef := by
  apply posSemidef_diagonal_iff.mpr
  intro i
  by_cases h : E i ≤ y <;> simp [h]

/-- A clock cutoff class in the algebra of measurable matrix fields. -/
def cutoffField (E : n → ℝ) : MatrixField n :=
  AEEqFun.mk (activeProjection E) (measurable_activeProjection E).aestronglyMeasurable

private theorem cutoffField_mul_self (E : n → ℝ) :
    cutoffField E * cutoffField E = cutoffField E := by
  apply AEEqFun.ext
  have hcut := AEEqFun.coeFn_mk (μ := volume) (activeProjection E)
    (measurable_activeProjection E).aestronglyMeasurable
  filter_upwards [AEEqFun.coeFn_mul (cutoffField E) (cutoffField E), hcut] with y hm hy
  change cutoffField E y = activeProjection E y at hy
  rw [hm, Pi.mul_apply, hy, activeProjection_sq]

private def cutoffCore (E : n → ℝ) : CoreField n :=
  ⟨cutoffField E, 1, (AEEqFun.coeFn_mk (activeProjection E)
    (measurable_activeProjection E).aestronglyMeasurable).mono fun y hy => by
      rw [show cutoffField E y = _ from hy, activeProjection, l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      split <;> simp⟩

/-- The positive-clock compression as a subring with its own multiplicative identity. -/
def ObserverCorner (E : n → ℝ) : NonUnitalSubring (CoreField n) := corner (cutoffCore E)

private theorem cutoffCore_mul_self (E : n → ℝ) : cutoffCore E * cutoffCore E = cutoffCore E :=
  Subtype.ext (cutoffField_mul_self E)

/-- The projection is the unit of the compressed algebra. -/
def observerUnit (E : n → ℝ) : ObserverCorner E := cornerUnit (cutoffCore_mul_self E)

instance (E : n → ℝ) : One (ObserverCorner E) := ⟨observerUnit E⟩

/-- The subring membership test is the two-sided compression equation. -/
theorem observerCorner_mem_iff (E : n → ℝ) (A : CoreField n) :
    A ∈ ObserverCorner E ↔ cutoffField E * A.val * cutoffField E = A.val :=
  (mem_corner_iff (cutoffCore_mul_self E) A).trans Subtype.ext_iff

/-- Translation from physical clock to total energy separately in each matter component. -/
def dress (E : n → ℝ) (ξ : n → ℝ → ℂ) (i : n) (y : ℝ) : ℂ :=
  ξ i (y - E i)

/-- The physical half-line cutoff becomes the spectral projection of the shifted energy. -/
theorem dressed_clock_cutoff (E : n → ℝ) (ξ : n → ℝ → ℂ) (y : ℝ) (i : n) :
    dress E (fun j x => if 0 ≤ x then ξ j x else 0) i y =
      (activeProjection E y *ᵥ fun j => dress E ξ j y) i := by
  simp only [dress, activeProjection, mulVec_diagonal, sub_nonneg]
  split <;> simp_all

/-- The faithful Gibbs matter state. -/
def gibbsState [Nonempty n] (β : ℝ) (E : n → ℝ) : DensityState n :=
  ⟨CStarMatrix.ofMatrix (diagonal fun i => (gibbsWeight β E i : ℂ)),
    by
      apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      rw [Matrix.nonneg_iff_posSemidef]
      exact posSemidef_diagonal_iff.mpr fun i =>
        Complex.zero_le_real.mpr (div_nonneg (Real.exp_pos (-β * E i)).le (partition_pos β E).le), by
    change (diagonal fun i => (gibbsWeight β E i : ℂ)).trace = 1
    rw [trace_diagonal, ← Complex.ofReal_sum, sum_gibbsWeight, Complex.ofReal_one]⟩

/-- The positive-cone weight of the full, uncut total-energy algebra. -/
def coreWeight (β : ℝ) (E : n → ℝ) (A : MatrixField n) : ℝ≥0∞ :=
  weight (totalWeight β E) A

/-- Weighted complex matrix trace. On the bounded clock corner the integrand is integrable. -/
def observerTrace (β : ℝ) (E : n → ℝ) (A : MatrixField n) : ℂ :=
  weightedTrace (totalWeight β E) A

omit [DecidableEq n] in
private theorem observerTrace_mk (β : ℝ) (E : n → ℝ) (A : ℝ → Matrix n n ℂ)
    (hA : AEStronglyMeasurable A volume) :
    observerTrace β E (AEEqFun.mk A hA) =
      ∫ y, (totalWeight β E y : ℂ) * Matrix.trace (A y) :=
  integral_congr_ae ((AEEqFun.coeFn_mk A hA).mono fun y h => by dsimp; rw [h])

omit [DecidableEq n] in
/-- Cyclicity uses the ordinary matrix trace in each total-energy fiber. -/
theorem observer_trace_mul_comm (β : ℝ) (E : n → ℝ) (A B : MatrixField n) :
    observerTrace β E (A * B) = observerTrace β E (B * A) := by
  apply integral_congr_ae
  filter_upwards [AEEqFun.coeFn_mul A B, AEEqFun.coeFn_mul B A] with y hAB hBA
  simp only [hAB, hBA, Pi.mul_apply, Matrix.trace_mul_comm (A y) (B y)]

/-- An ordered matter and physical-clock moment in the total-energy representation. -/
def clockObservable (E : n → ℝ) (A : Matrix n n ℂ) (f : ℝ → ℝ) (y : ℝ) :
    Matrix n n ℂ :=
  activeProjection E y * A * diagonal (fun i => (f (y - E i) : ℂ)) * activeProjection E y

private theorem clockObservable_apply_diag (E : n → ℝ) (A : Matrix n n ℂ) (f : ℝ → ℝ)
    (y : ℝ) (i : n) :
    clockObservable E A f y i i = if E i ≤ y then (f (y - E i) : ℂ) * A i i else 0 := by
  simp only [clockObservable, activeProjection, mul_diagonal, diagonal_mul]
  split <;> simp_all [mul_comm]

private theorem measurable_clockObservable (E : n → ℝ) (A : Matrix n n ℂ)
    {f : ℝ → ℝ} (hf : Measurable f) : Measurable (clockObservable E A f) := by
  have hd : Measurable fun y : ℝ => diagonal fun i => (f (y - E i) : ℂ) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    by_cases h : i = j
    · subst j
      simp only [diagonal_apply_eq]
      exact Complex.continuous_ofReal.measurable.comp (hf.comp (by fun_prop))
    · simp [diagonal_apply_ne _ h]
  exact (((measurable_activeProjection E).mul measurable_const).mul hd).mul
    (measurable_activeProjection E)

/-- The observer trace of an ordered moment factors into its Gibbs and clock values. -/
theorem gibbs_clock_moments [Nonempty n] {β : ℝ} (hβ : 0 < β) (E : n → ℝ)
    (A : Matrix n n ℂ) (f : ℝ → ℝ) (hf : Measurable f) (hC : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    observerTrace β E (AEEqFun.mk (clockObservable E A f)
        (measurable_clockObservable E A hf).aestronglyMeasurable) =
      (Matrix.trace (CStarMatrix.ofMatrix.symm (gibbsState β E).1 * A)) *
        ((∫ x in Ici (0 : ℝ), clockWeight β x * f x : ℝ) : ℂ) := by
  obtain ⟨C, hC⟩ := hC
  let g (i : n) (y : ℝ) : ℂ := (totalWeight β E y * f (y - E i) : ℝ) * A i i
  have hg (i : n) : IntegrableOn (g i) (Ici (E i)) := by
    exact ((integrableOn_clock_times hβ hf C hC E i).ofReal).mul_const _
  rw [observerTrace_mk]
  have hsum : (fun y => (totalWeight β E y : ℂ) * (clockObservable E A f y).trace) =
      fun y => ∑ i, (Ici (E i)).indicator (g i) y := by
    funext y
    simp only [Matrix.trace, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [diag_apply, clockObservable_apply_diag]
    by_cases h : E i ≤ y <;> simp [g, h, mul_assoc]
  rw [hsum, integral_finsetSum _ (fun i _ => (hg i).integrable_indicator measurableSet_Ici)]
  simp only [integral_indicator measurableSet_Ici]
  simp only [g, integral_mul_const]
  change _ = (diagonal (fun i => (gibbsWeight β E i : ℂ)) * A).trace * _
  simp only [Matrix.trace, diag_apply, diagonal_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_complex_ofReal, integral_shifted_clock, Complex.ofReal_mul]
  ring

/-- The trace of the cutoff unit is one. -/
theorem observer_trace_one [Nonempty n] {β : ℝ} (hβ : 0 < β) (E : n → ℝ) :
    observerTrace β E (cutoffField E) = 1 := by
  have h : clockObservable E (1 : Matrix n n ℂ) (fun _ => 1) = activeProjection E := by
    funext y
    simp [clockObservable, activeProjection_sq]
  have hm := gibbs_clock_moments hβ E 1 (fun _ => 1) measurable_const ⟨1, by simp⟩
  rw [show (AEEqFun.mk (clockObservable E 1 (fun _ => 1))
      (measurable_clockObservable E 1 measurable_const).aestronglyMeasurable) = cutoffField E from
    AEEqFun.mk_eq_mk.mpr (Filter.Eventually.of_forall (congrFun h))] at hm
  have hg : (CStarMatrix.ofMatrix.symm (gibbsState β E).1).trace = 1 :=
    (gibbsState β E).2.2
  calc
    _ = _ := hm
    _ = 1 := by
      rw [Matrix.mul_one, hg, one_mul]
      norm_cast
      simpa only [mul_one] using integral_clockWeight hβ

omit [DecidableEq n] in
private theorem measurable_totalWeight (β : ℝ) (E : n → ℝ) : Measurable (totalWeight β E) := by
  unfold totalWeight
  fun_prop

/-- Faithfulness on the positive cone of measurable matrix fields. -/
theorem coreWeight_faithful [Nonempty n] {β : ℝ} (hβ : 0 < β) (E : n → ℝ)
    (A : MatrixField n) (hA : ∀ᵐ y ∂volume, (A y).PosSemidef) :
    coreWeight β E A = 0 ↔ A = 0 :=
  Omega.MeasureTheory.MatrixFieldEntropy.weight_faithful (measurable_totalWeight β E)
    (totalWeight_pos hβ E) A hA

/-- The uncut weight is semifinite on bounded positive fields. -/
theorem coreWeight_semifinite [Nonempty n] {β : ℝ} (hβ : 0 < β) (E : n → ℝ)
    (A : CoreField n) (hp : ∀ᵐ x ∂volume, 0 ≤ A.1 x) :
    ∃ B : ℕ → CoreField n, (∀ k, (∀ᵐ x ∂volume, 0 ≤ (B k).1 x ∧ (B k).1 x ≤ A.1 x) ∧
      coreWeight β E (B k).1 ≠ ∞) ∧ coreWeight β E A.1 = ⨆ k, coreWeight β E (B k).1 := by
  obtain ⟨B, hB, hsup⟩ :=
    Omega.MeasureTheory.MatrixFieldEntropy.totalWeight_semifinite hβ E A.1 A.2 hp
  exact ⟨fun k => ⟨B k, (hB k).1⟩, fun k => (hB k).2, hsup⟩

private theorem integrable_observerTrace [Nonempty n] {β : ℝ} (hβ : 0 < β)
    (E : n → ℝ) (A : ObserverCorner E) :
    Integrable (fun y => (totalWeight β E y : ℂ) * ((A.1.1 : MatrixField n) y).trace) := by
  let a : MatrixField n := A.1.1
  let levels := Finset.univ.image E
  let bottom := levels.min' (Finset.univ_nonempty.image E)
  let tr : Matrix n n ℂ →L[ℂ] ℂ :=
    (Matrix.traceLinearMap (n := n) ℂ ℂ).toContinuousLinearMap
  refine integrable_weighted_linear a A.1.2 tr measurableSet_Ici
    (measurable_totalWeight β E) (fun y => (totalWeight_pos hβ E y).le)
    (integrableOn_totalWeight hβ E bottom) ?_
  have hcut := AEEqFun.coeFn_mk (μ := volume) (activeProjection E)
    (measurable_activeProjection E).aestronglyMeasurable
  filter_upwards [hcut, AEEqFun.coeFn_mul (cutoffField E) a] with y hP hAx hy
  have hzero : activeProjection E y = 0 := by
    have heq : (fun i => if E i ≤ y then (1 : ℂ) else 0) = 0 := by
      funext i
      have hmin : bottom ≤ E i :=
        Finset.min'_le levels _ (Finset.mem_image_of_mem E (Finset.mem_univ i))
      simp only [mem_Ici, not_le] at hy
      exact ite_eq_right (not_le.mpr (hy.trans_le hmin))
    simp [activeProjection, heq]
  have hcomp : cutoffField E * a = a := congrArg (fun B : CoreField n => B.val) A.2.1
  rw [hcomp, Pi.mul_apply, show cutoffField E y = _ from hP, hzero, zero_mul] at hAx
  exact hAx

/-- The complex corner trace restricts to a faithful weight on positive fields. -/
theorem observer_trace_faithful [Nonempty n] {β : ℝ} (hβ : 0 < β) (E : n → ℝ)
    (A : ObserverCorner E) (hA : ∀ᵐ y ∂volume, (A.1.1 y).PosSemidef) :
    observerTrace β E A.1.1 = 0 ↔ A.1.1 = 0 :=
  Omega.MeasureTheory.MatrixFieldEntropy.weightedTrace_faithful (measurable_totalWeight β E)
    (totalWeight_pos hβ E) A.1.1 hA (integrable_observerTrace hβ E A)

omit [Fintype n] in
private theorem activeComplement_pos (E : n → ℝ) (y : ℝ) :
    ((1 : Matrix n n ℂ) - activeProjection E y).PosSemidef := by
  have heq : ((1 : Matrix n n ℂ) - activeProjection E y) =
      diagonal (fun i => (1 : ℂ) - (if E i ≤ y then 1 else 0)) := by
    ext i j
    by_cases h : i = j <;> simp [activeProjection, h]
  rw [heq]
  apply posSemidef_diagonal_iff.mpr
  intro i
  by_cases h : E i ≤ y <;> simp [h]

/-- A positive trace-one density may be an unbounded measurable field. -/
abbrev TraceDensity (β : ℝ) (E : n → ℝ) :=
  Omega.MeasureTheory.MatrixFieldEntropy.Density (totalWeight β E) (cutoffField E)

/-- Extended trace entropy. An infinite integral of the gap gives entropy minus infinity. -/
def traceEntropy {β : ℝ} {E : n → ℝ} (ρ : TraceDensity β E) : EReal :=
  Omega.MeasureTheory.MatrixFieldEntropy.traceEntropy (measurable_activeProjection E) ρ

/-- The normalized trace entropy is bounded above by zero. -/
theorem trace_entropy_le_zero {β : ℝ} {E : n → ℝ} (ρ : TraceDensity β E) :
    traceEntropy ρ ≤ 0 :=
  Omega.MeasureTheory.MatrixFieldEntropy.trace_entropy_le_zero (measurable_activeProjection E) ρ

/-- The unique maximizing density is the cutoff unit as an almost everywhere class. -/
theorem trace_entropy_eq_zero_iff [Nonempty n] {β : ℝ} (hβ : 0 < β) {E : n → ℝ}
    (ρ : TraceDensity β E) : traceEntropy ρ = 0 ↔ ρ.field = cutoffField E :=
  Omega.MeasureTheory.MatrixFieldEntropy.trace_entropy_eq_zero_iff (measurable_totalWeight β E)
    (totalWeight_pos hβ E) (measurable_activeProjection E) (activeComplement_pos E) ρ

private abbrev paddedEntropyTrace (E : n → ℝ) :=
  Omega.MeasureTheory.MatrixFieldEntropy.paddedEntropyTrace (μ := volume) (activeProjection E)

/-- At finite logarithmic integral, the gap entropy equals minus the tracial log integral. -/
theorem traceEntropy_eq_neg_integral [Nonempty n] {β : ℝ} (hβ : 0 < β) {E : n → ℝ}
    (ρ : TraceDensity β E)
    (hℓ : Integrable (fun y => totalWeight β E y * paddedEntropyTrace E ρ.field y)) :
    traceEntropy ρ = (-(∫ y, totalWeight β E y * paddedEntropyTrace E ρ.field y) : ℝ) :=
  Omega.MeasureTheory.MatrixFieldEntropy.traceEntropy_eq_neg_integral (measurable_totalWeight β E)
    (totalWeight_pos hβ E) (measurable_activeProjection E) (activeComplement_pos E)
    (integrable_observerTrace hβ E (observerUnit E)) (observer_trace_one hβ E) ρ hℓ

/-- The classical density relative to its clock and matter Gibbs factors. -/
def cqScale (β : ℝ) (E : n → ℝ) (p : ℝ → ℝ) (e x : ℝ) : ℝ :=
  p x / clockWeight β x / (Real.exp (-β * e) / partition β E)

/-- The positive-clock density of a state restricted to the equal-energy blocks. -/
def cqDensity (β : ℝ) (E : n → ℝ) (p : ℝ → ℝ) (σ : ℝ → DensityState n) :
    ℝ → Matrix n n ℂ :=
  shiftedEnergyDensity E (cqScale β E p) (fun x => CStarMatrix.ofMatrix.symm (σ x).1)

private theorem measurable_cqDensity (β : ℝ) (E : n → ℝ) {p : ℝ → ℝ}
    (σ : ℝ → DensityState n) (hp : Measurable p)
    (hσ : Measurable fun x => CStarMatrix.ofMatrix.symm (σ x).1) :
    Measurable (cqDensity β E p σ) := by
  apply measurable_shiftedEnergyDensity E _ _ _ hσ
  intro e
  unfold cqScale clockWeight
  fun_prop

private theorem cqDensity_pos [Nonempty n] {β : ℝ} (hβ : 0 < β) (E : n → ℝ)
    {p : ℝ → ℝ} (hp : ∀ x, 0 ≤ p x) (σ : ℝ → DensityState n) (y : ℝ) :
    (cqDensity β E p σ y).PosSemidef := by
  apply shiftedEnergyDensity_pos E
  · intro e x
    exact div_nonneg (div_nonneg (hp x) (mul_pos hβ (Real.exp_pos _)).le)
      (div_nonneg (Real.exp_pos _).le (partition_pos β E).le)
  · intro x
    exact (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (σ x).2.1).posSemidef

private theorem cqDensity_mass [Nonempty n] {β : ℝ} (hβ : 0 < β) (E : n → ℝ)
    {p : ℝ → ℝ} (hp : Measurable p) (hn : ∀ x, 0 ≤ p x)
    (hp1 : ∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal (p x) = 1)
    (σ : ℝ → DensityState n) (hσ : Measurable fun x => CStarMatrix.ofMatrix.symm (σ x).1) :
    (∫⁻ y, ENNReal.ofReal (totalWeight β E y * (cqDensity β E p σ y).trace.re)) = 1 := by
  let A := fun x => CStarMatrix.ofMatrix.symm (σ x).1
  let f := fun (i : n) x => p x * (A x i i).re
  have hf (i : n) : Measurable (fun x => ENNReal.ofReal (f i x)) :=
    (hp.mul (Complex.continuous_re.measurable.comp ((measurable_pi_apply i).comp ((measurable_pi_apply i).comp hσ)))).ennreal_ofReal
  have hfn (i : n) (x : ℝ) : 0 ≤ f i x := mul_nonneg (hn x) (Complex.nonneg_iff.mp
    ((map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (σ x).2.1).posSemidef.diag_nonneg (i := i))).1
  have hsum : (fun y => ENNReal.ofReal (totalWeight β E y * (cqDensity β E p σ y).trace.re)) =
      fun y => ∑ i, (Ici (E i)).indicator (fun z => ENNReal.ofReal (f i (z - E i))) y := by
    funext y
    have hentry (i : n) : totalWeight β E y * (cqDensity β E p σ y i i).re =
        if E i ≤ y then f i (y - E i) else 0 := by
      by_cases hy : E i ≤ y
      · rw [show y = y - E i + E i by ring, totalWeight_shift]
        simp only [cqDensity, shiftedEnergyDensity, eq_self, true_and, ite_eq_left
          (show E i ≤ y - E i + E i by simpa), add_sub_cancel_right]
        simp only [cqScale, gibbsWeight, f, A, Complex.real_smul, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        field_simp [clockWeight, hβ.ne', Real.exp_ne_zero, (partition_pos β E).ne']
      · simp [cqDensity, shiftedEnergyDensity, hy]
    simp only [Matrix.trace, Complex.re_sum, Matrix.diag_apply, Finset.mul_sum, hentry]
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by split <;> simp_all)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hy : E i ≤ y <;> simp [hy]
  rw [hsum, lintegral_shifted_sum E _ hf]
  convert hp1 using 1
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hfn i x)]
  congr 1
  have hs : ∑ i, (A x i i).re = 1 := by
    have hh : (A x).trace = 1 := (σ x).2.2
    simpa only [Matrix.trace, Complex.re_sum, Matrix.diag_apply, Complex.one_re] using
      congrArg Complex.re hh
  simp only [f, ← Finset.mul_sum, hs, mul_one]

/-- A normalized cq state induces a positive trace-one density in the cutoff corner. -/
def cqTraceDensity [Nonempty n] {β : ℝ} (hβ : 0 < β) (E : n → ℝ) {p : ℝ → ℝ}
    (hp : Measurable p) (hn : ∀ x, 0 ≤ p x)
    (hp1 : ∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal (p x) = 1)
    (σ : ℝ → DensityState n) (hσ : Measurable fun x => CStarMatrix.ofMatrix.symm (σ x).1) :
    TraceDensity β E := by
  let f := cqDensity β E p σ
  have hm := (measurable_cqDensity β E σ hp hσ).aestronglyMeasurable (μ := volume)
  let A := AEEqFun.mk f hm
  have hA := AEEqFun.coeFn_mk f hm
  have hpos : ∀ᵐ y ∂volume, (A y).PosSemidef :=
    hA.mono fun y hy => by
      rw [hy]
      exact cqDensity_pos hβ E hn σ y
  refine ⟨A, hpos, ?_, ?_⟩
  · apply AEEqFun.ext
    filter_upwards [hA, AEEqFun.coeFn_mk (μ := volume) (activeProjection E)
      (measurable_activeProjection E).aestronglyMeasurable,
      AEEqFun.coeFn_mul (cutoffField E) A,
      AEEqFun.coeFn_mul (cutoffField E * A) (cutoffField E)] with y hy hP hm₁ hm₂
    change (cutoffField E * A * cutoffField E) y = A y
    rw [hm₂, Pi.mul_apply, hm₁, Pi.mul_apply, show cutoffField E y = _ from hP, hy]
    exact shiftedEnergyDensity_compressed E _ _ y
  · unfold weight
    refine (lintegral_congr_ae (hA.mono fun y hy =>
      congrArg (fun M : Matrix n n ℂ => ENNReal.ofReal (totalWeight β E y * M.trace.re)) hy)).trans ?_
    exact cqDensity_mass hβ E hp hn hp1 σ hσ

theorem cqTraceDensity_field_ae [Nonempty n] {β : ℝ} (hβ : 0 < β) (E : n → ℝ)
    {p : ℝ → ℝ} (hp : Measurable p) (hn : ∀ x, 0 ≤ p x)
    (hp1 : ∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal (p x) = 1)
    (σ : ℝ → DensityState n) (hσ : Measurable fun x => CStarMatrix.ofMatrix.symm (σ x).1) :
    (cqTraceDensity hβ E hp hn hp1 σ hσ).field =ᵐ[volume] cqDensity β E p σ :=
  AEEqFun.coeFn_mk _ _


private abbrev stateMatrix (ρ : DensityState n) : Matrix n n ℂ := CStarMatrix.ofMatrix.symm ρ.1

private theorem stateMatrix_pos (ρ : DensityState n) : (stateMatrix ρ).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1)

/-- The restriction of a matter density to the energy blocks. -/
def pinchedState (E : n → ℝ) (ρ : DensityState n) : DensityState n :=
  ⟨CStarMatrix.ofMatrix (energyPinching E (stateMatrix ρ)),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (pinching_pos E (stateMatrix_pos ρ)).nonneg,
    by simpa [Matrix.trace, Matrix.diag, energyPinching] using ρ.2.2⟩

private theorem quantumRelativeEntropy_eq_traceLog (A B : DensityState n) :
    quantumRelativeEntropy A B = traceLogDivergence (stateMatrix A) (stateMatrix B) := by
  rw [quantum_relative_entropy_eq_neg_entropy_sub_cross, vonNeumannEntropy, neg_neg]
  rfl

/-- Negative relative entropy to the product of an exponential clock and a matter reference. -/
def cqNegativeRelativeEntropy (β : ℝ) (p : ℝ → ℝ) (σ : ℝ → DensityState n)
    (ω : DensityState n) : ℝ :=
  -(∫ x in Ici (0 : ℝ), p x *
    (Real.log (p x / clockWeight β x) + quantumRelativeEntropy (σ x) ω))


open D5.S3.Quantum.Lieb.PositiveMapJensen (cfc_intertwining)
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (cfc_log_diagonal)

private theorem cq_pad_cfc_diag [Nonempty n] {β : ℝ} (hβ : 0 < β) (E : n → ℝ)
    (p : ℝ → ℝ) (σ : ℝ → DensityState n) (hp : ∀ x, 0 ≤ p x)
    (hσ : ∀ x i j, E i ≠ E j → stateMatrix (σ x) i j = 0) (y : ℝ) (i : n) :
    cfc xlogx (cqDensity β E p σ y + (1 - activeProjection E y)) i i =
      if E i ≤ y then cfc xlogx (cqScale β E p (E i) (y - E i) •
        stateMatrix (σ (y - E i))) i i else 0 := by
  let A := cqDensity β E p σ y + (1 - activeProjection E y)
  let B : Matrix n n ℂ := if E i ≤ y then cqScale β E p (E i) (y - E i) •
    stateMatrix (σ (y - E i)) else 1
  have hB : B.IsHermitian := by
    by_cases hi : E i ≤ y
    · have hs : 0 ≤ cqScale β E p (E i) (y - E i) := by
        unfold cqScale clockWeight
        exact div_nonneg (div_nonneg (hp _) (mul_pos hβ (Real.exp_pos _)).le)
          (div_nonneg (Real.exp_pos _).le (partition_pos β E).le)
      simpa only [B, ite_eq_left hi] using ((stateMatrix_pos (σ (y - E i))).smul hs).isHermitian
    · simp [B, hi]
  have hrel : A * energyProjection E (E i) = energyProjection E (E i) * B :=
    shiftedEnergyDensity_padded_intertwine E (cqScale β E p) _ hσ y i
  have hc := cfc_intertwining A B ((cqDensity_pos hβ E hp σ y).add
    (activeComplement_pos E y)).isHermitian hB (energyProjection E (E i)) hrel xlogx
  have hi : cfc xlogx A i i = cfc xlogx B i i := by
    simpa [energyProjection, mul_diagonal, diagonal_mul] using
      congrArg (fun M : Matrix n n ℂ => M i i) hc
  change cfc xlogx A i i = _
  rw [hi]
  by_cases h : E i ≤ y
  · simp [B, h]
  · simp only [B, ite_eq_right h]
    rw [show (1 : Matrix n n ℂ) = algebraMap ℝ (Matrix n n ℂ) 1 from (map_one _).symm,
      cfc_algebraMap]
    simp [xlogx]

private theorem cq_pointwise_log (w : n → ℝ) (σ ω : DensityState n)
    (hω : stateMatrix ω = diagonal (fun i => (w i : ℂ))) (hw : ∀ i, 0 < w i)
    {p q : ℝ} (hq : 0 < q) :
    (∑ i, q * w i * (cfc xlogx ((p / q / w i) • stateMatrix σ) i i).re) =
      p * (Real.log (p / q) + quantumRelativeEntropy σ ω) := by
  have ht : (stateMatrix σ).trace.re = 1 := by
    change (Matrix.trace σ.1).re = 1
    rw [σ.2.2]
    simp
  have hlog : CFC.log (stateMatrix ω) =
      diagonal (fun i => (Real.log (w i) : ℂ)) := by rw [hω, cfc_log_diagonal]
  rw [weighted_xlogx_trace _ (stateMatrix_pos σ).isHermitian ht w hw hq, ← hlog,
    quantum_relative_entropy_eq_neg_entropy_sub_cross, vonNeumannEntropy, neg_neg]
  change p * (Real.log (p / q) + (σ.1 * CFC.log σ.1).trace.re - (σ.1 * CFC.log ω.1).trace.re) = _
  ring

private def cqPhysicalTraceLogDiag (E : n → ℝ) (β : ℝ) (p : ℝ → ℝ)
    (σ : ℝ → DensityState n) (i : n) (x : ℝ) : ℝ :=
  (cfc xlogx ((p x / clockWeight β x / gibbsWeight β E i) • stateMatrix (σ x)) i i).re

private theorem cq_traceEntropy_eq_negativeRelativeEntropy [Nonempty n] {β : ℝ}
    (hβ : 0 < β) (E : n → ℝ) {p : ℝ → ℝ} (hp : Measurable p) (hn : ∀ x, 0 ≤ p x)
    (hp1 : ∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal (p x) = 1)
    (σ : ℝ → DensityState n) (hσm : Measurable fun x => stateMatrix (σ x))
    (hσ : ∀ x i j, E i ≠ E j → stateMatrix (σ x) i j = 0)
    (hdiag : ∀ i, IntegrableOn (fun x => clockWeight β x *
      cqPhysicalTraceLogDiag E β p σ i x) (Ici 0)) :
    traceEntropy (cqTraceDensity hβ E hp hn hp1 σ hσm) =
      (cqNegativeRelativeEntropy β p σ (gibbsState β E) : EReal) := by
  let ρ := cqTraceDensity hβ E hp hn hp1 σ hσm
  have hρ : ∀ᵐ y ∂volume, ρ.field y = cqDensity β E p σ y :=
    cqTraceDensity_field_ae hβ E hp hn hp1 σ hσm
  let f := cqPhysicalTraceLogDiag E β p σ
  let g (i : n) (y : ℝ) := totalWeight β E y * f i (y - E i)
  have hsum : (fun y => totalWeight β E y *
      (cfc xlogx (cqDensity β E p σ y +
        (1 - activeProjection E y))).trace.re) =
      fun y => ∑ i, (Ici (E i)).indicator (g i) y := by
    funext y
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cq_pad_cfc_diag hβ E p σ hn hσ y i]
    by_cases h : E i ≤ y <;> simp [indicator, h, g, f, cqScale, gibbsWeight, cqPhysicalTraceLogDiag]
  obtain ⟨hint, hchange⟩ := integral_shifted_sum E β f hdiag
  have hfield : (fun y => totalWeight β E y * paddedEntropyTrace E ρ.field y) =ᵐ[volume]
      fun y => ∑ i, (Ici (E i)).indicator (g i) y := by
    rw [← hsum]
    exact hρ.mono fun y hy => by
      change totalWeight β E y * (cfc xlogx (ρ.field y + (1 - activeProjection E y))).trace.re = _
      rw [hy]
  have htranslate : (∫ y, ∑ i, (Ici (E i)).indicator (g i) y) =
      ∫ x in Ici 0, ∑ i, gibbsWeight β E i * (clockWeight β x * f i x) := hchange
  rw [traceEntropy_eq_neg_integral hβ ρ (hint.congr hfield.symm),
    integral_congr_ae hfield, htranslate, cqNegativeRelativeEntropy]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with x
  simp_rw [mul_left_comm (gibbsWeight β E _) (clockWeight β x), ← mul_assoc]
  exact cq_pointwise_log _ (σ x) (gibbsState β E) rfl
    (fun _ => div_pos (Real.exp_pos _) (partition_pos β E)) (mul_pos hβ (Real.exp_pos _))

private theorem cq_finite [Nonempty n] {β : ℝ} (hβ : 0 < β) (E : n → ℝ)
    (p : ℝ → ℝ) (σ : ℝ → DensityState n) (hσ : Measurable fun x => stateMatrix (σ x))
    (hp : IntegrableOn p (Ici 0))
    (hl : IntegrableOn (fun x => p x * Real.log (p x / clockWeight β x)) (Ici 0)) :
    (∀ i, IntegrableOn (fun x => clockWeight β x * cqPhysicalTraceLogDiag E β p σ i x) (Ici 0)) ∧
      IntegrableOn (fun x => p x * (Real.log (p x / clockWeight β x) +
        quantumRelativeEntropy (σ x) (gibbsState β E))) (Ici 0) := by
  have hg (i : n) : 0 < gibbsWeight β E i :=
    div_pos (Real.exp_pos _) (partition_pos β E)
  have hq (x : ℝ) : 0 < clockWeight β x := mul_pos hβ (Real.exp_pos _)
  have ht (x : ℝ) : (stateMatrix (σ x)).trace.re = 1 := by
    change (Matrix.trace (σ x).1).re = 1
    rw [(σ x).2.2, Complex.one_re]
  have hd (i : n) : IntegrableOn (fun x =>
      clockWeight β x * cqPhysicalTraceLogDiag E β p σ i x) (Ici 0) :=
    integrable_weighted_xlogx_diagonal _ hσ (fun x => stateMatrix_pos (σ x)) ht
      p (clockWeight β) (hg i) hq hp hl i
  refine ⟨hd, (integrable_finsetSum Finset.univ fun i _ =>
    (hd i).const_mul (gibbsWeight β E i)).congr (Filter.Eventually.of_forall fun x => ?_)⟩
  change (∑ i, gibbsWeight β E i * (clockWeight β x * cqPhysicalTraceLogDiag E β p σ i x)) = _
  simp_rw [mul_left_comm (gibbsWeight β E _) (clockWeight β x), ← mul_assoc]
  exact cq_pointwise_log _ (σ x) (gibbsState β E) rfl hg (hq x)

private theorem gibbsState_commutes [Nonempty n] (β : ℝ) (E : n → ℝ) :
    Commute (stateMatrix (gibbsState β E)) (energyDiagonal E) := by
  change Commute (diagonal fun i => (gibbsWeight β E i : ℂ)) (energyDiagonal E)
  rw [energyDiagonal]
  exact Matrix.commute_diagonal _ _

private theorem measurable_pinchedState (E : n → ℝ) (σ : ℝ → DensityState n)
    (hσ : Measurable (fun x => stateMatrix (σ x))) :
    Measurable fun x => stateMatrix (pinchedState E (σ x)) := by
  apply Measurable.of_eval_matrix
  intro i j
  change Measurable (fun x => energyPinching E (stateMatrix (σ x)) i j)
  by_cases he : E i = E j
  · simpa only [energyPinching, ite_eq_left he] using (hσ.eval_matrix (i := i) (j := j))
  · simp [energyPinching, he]

/-- In the Gibbs centralizer, the normalized corner entropy splits into the
clock differential entropy, observer energy, matter relative entropy, and log beta. -/
theorem observer_generalized_entropy [Nonempty n] {β : ℝ} (hβ : 0 < β) (E : n → ℝ)
    (p : ℝ → ℝ) (hp : Measurable p) (hn : ∀ x, 0 ≤ p x)
    (hm : ∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal (p x) = 1)
    (σ : ℝ → DensityState n) (hσm : Measurable fun x => stateMatrix (σ x))
    (hσ : ∀ x, Commute (stateMatrix (σ x)) (energyDiagonal E))
    (hpl : IntegrableOn (fun x => p x * Real.log (p x)) (Ici 0))
    (hxp : IntegrableOn (fun x => x * p x) (Ici 0)) :
    traceEntropy (cqTraceDensity hβ E hp hn hm σ hσm) =
      ((-(∫ x in Ici (0 : ℝ), p x * (β * x + quantumRelativeEntropy (σ x) (gibbsState β E))) -
        (∫ x in Ici (0 : ℝ), p x * Real.log (p x)) + Real.log β : ℝ) : EReal) := by
  obtain ⟨hpi, hm', hl⟩ := finite_clock_log hβ hp hn hm hpl hxp
  obtain ⟨hd, hi⟩ := cq_finite hβ E p σ hσm hpi hl
  have hoff (x : ℝ) (i j : n) (he : E i ≠ E j) : stateMatrix (σ x) i j = 0 := by
    have h := (energyPinching_eq_self_iff E _).mpr (hσ x)
    simpa [energyPinching, he] using (congrFun (congrFun h i) j).symm
  rw [cq_traceEntropy_eq_negativeRelativeEntropy hβ E hp hn hm σ hσm hoff hd]
  have hpm : IntegrableOn (fun x => p x *
      (β * x + quantumRelativeEntropy (σ x) (gibbsState β E))) (Ici 0) := by
    refine ((hi.sub hpl).add (hpi.const_mul (Real.log β))).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, Pi.add_apply, mul_add, log_clock_mul hβ]
    ring
  exact congrArg (fun t : ℝ => (t : EReal)) (negative_clock_relative_entropy_split hβ p
    (fun x => quantumRelativeEntropy (σ x) (gibbsState β E)) hpi hm' hpl hpm)

/-- The trace entropy gained by restricting to the physical-clock algebra is the
weighted relative entropy to the energy-block pinching. -/
theorem observer_entropy_coherence_defect [Nonempty n] {β : ℝ} (hβ : 0 < β) (E : n → ℝ)
    (p : ℝ → ℝ) (hp : Measurable p) (hn : ∀ x, 0 ≤ p x)
    (hm : ∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal (p x) = 1)
    (σ : ℝ → DensityState n) (hσm : Measurable fun x => stateMatrix (σ x))
    (hpl : IntegrableOn (fun x => p x * Real.log (p x)) (Ici 0))
    (hxp : IntegrableOn (fun x => x * p x) (Ici 0)) :
    let σ₀ := fun x => pinchedState E (σ x)
    let C := ∫ x in Ici (0 : ℝ), p x * quantumRelativeEntropy (σ x) (σ₀ x)
    traceEntropy (cqTraceDensity hβ E hp hn hm σ₀ (measurable_pinchedState E σ hσm)) =
      ((cqNegativeRelativeEntropy β p σ (gibbsState β E) + C : ℝ) : EReal) ∧ 0 ≤ C ∧
      (C = 0 ↔ ∀ᵐ x ∂(volume.restrict (Ici 0)).withDensity (fun x => ENNReal.ofReal (p x)),
        Commute (stateMatrix (σ x)) (energyDiagonal E)) := by
  let σ₀ := fun x => pinchedState E (σ x)
  let C := ∫ x in Ici (0 : ℝ), p x * quantumRelativeEntropy (σ x) (σ₀ x)
  obtain ⟨hpi, _, hl⟩ := finite_clock_log hβ hp hn hm hpl hxp
  obtain ⟨_, hi⟩ := cq_finite hβ E p σ hσm hpi hl
  have hσ₀m : Measurable fun x => stateMatrix (σ₀ x) := measurable_pinchedState E σ hσm
  obtain ⟨hd, hi₀⟩ := cq_finite hβ E p σ₀ hσ₀m hpi hl
  have hσ₀ (x : ℝ) (i j : n) (he : E i ≠ E j) : stateMatrix (σ₀ x) i j = 0 := by
    change energyPinching E (stateMatrix (σ x)) i j = 0
    simp [energyPinching, he]
  obtain ⟨hgap, hnonneg, hzero⟩ :=
    integrated_pinching_defect (volume.restrict (Ici 0)) E
      (fun x => stateMatrix (σ x)) (stateMatrix (gibbsState β E))
      (fun x => stateMatrix_pos (σ x)) (gibbsState_commutes β E)
      p (fun x => Real.log (p x / clockWeight β x)) hp hn
      (by
        change IntegrableOn _ (Ici (0 : ℝ))
        simpa only [quantumRelativeEntropy_eq_traceLog] using hi)
      (by
        change IntegrableOn _ (Ici (0 : ℝ))
        simp only [quantumRelativeEntropy_eq_traceLog] at hi₀
        exact hi₀)
  change traceEntropy (cqTraceDensity hβ E hp hn hm σ₀ hσ₀m) =
    ((cqNegativeRelativeEntropy β p σ (gibbsState β E) + C : ℝ) : EReal) ∧ _
  have hce : C = ∫ x in Ici (0 : ℝ), p x *
      traceLogDivergence (stateMatrix (σ x)) (energyPinching E (stateMatrix (σ x))) := by
    simp only [C, quantumRelativeEntropy_eq_traceLog]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [cq_traceEntropy_eq_negativeRelativeEntropy hβ E hp hn hm σ₀ hσ₀m hσ₀ hd]
    apply congrArg (fun r : ℝ => (r : EReal))
    rw [hce]
    unfold cqNegativeRelativeEntropy
    simp only [quantumRelativeEntropy_eq_traceLog]
    exact sub_eq_iff_eq_add'.mp hgap
  · change 0 ≤ C
    rwa [hce]
  · change C = 0 ↔ _
    rwa [hce]

end D5.S3.Quantum.Analysis.NullConeGravity.ObserverCrossedProductEntropy
