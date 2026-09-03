/- GID: D5/S3/Weil/ZetaLinear/FiniteInversePoissonCriterion
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaLinear/FiniteInversePoissonCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equate reflected finite-window criticality with positivity and boundedness. -/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Tactic

/-! Library-search audit trail (2026-09-03):
   * D5 searches for finite inverse-Poisson sums, positive-definite kernels,
     bounded character sums, reflected damping, and generalized critical-line
     criteria found adjacent damping and variance criteria, but no theorem with
     this three-way equivalence.
   * Pinned Mathlib has `Matrix.posSemidef_conjTranspose_mul_self` and
     `Matrix.PosSemidef.det_nonneg` for the positive-definite implications, but
     no positive-definite-function API or finite exponential-sum boundedness
     theorem.
   * LeanSearch/Loogle queries for bounded finite exponential sums and
     recurrence of compact-group powers returned no exact result. The needed
     noncancellation argument is proved below from Bolzano-Weierstrass via
     `Metric.tendsto_subseq_of_bounded`, rather than assumed.
   * The finite family carries an explicit same-ordinate sign-reversing
     permutation. This is the exact functional-equation input used in the
     source proof. The empty window is intentionally allowed: all three
     conditions then hold. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion

open Complex Filter Matrix Metric Set
open scoped BigOperators ComplexConjugate ComplexOrder Topology

/-- A finite positive-ordinate zero window, expressed by its displacement from
the critical line and its ordinate. The permutation is the functional-equation
pairing at a fixed ordinate. -/
structure FinitePoissonWindow (n : ℕ) where
  displacement : Fin n → ℝ
  ordinate : Fin n → ℝ
  reflect : Equiv.Perm (Fin n)
  displacement_reflect : ∀ i, displacement (reflect i) = -displacement i
  ordinate_reflect : ∀ i, ordinate (reflect i) = ordinate i

/-- The unitary phase attached to one zero ordinate. -/
def phase {n : ℕ} (window : FinitePoissonWindow n) (t : ℝ) (i : Fin n) : ℂ :=
  Complex.exp ((window.ordinate i * t : ℝ) * Complex.I)

/-- The finite-window inverse-Poisson sum
`sum exp (-delta |t|) exp (i gamma t)`. -/
def inversePoissonSum {n : ℕ} (window : FinitePoissonWindow n) (t : ℝ) : ℂ :=
  ∑ i, (Real.exp (-window.displacement i * |t|) : ℂ) * phase window t i

/-- Positive definiteness on the additive real group, in the standard finite
positive-semidefinite-matrix formulation. -/
def PositiveDefinite (f : ℝ → ℂ) : Prop :=
  ∀ (m : ℕ) (x : Fin m → ℝ),
    Matrix.PosSemidef (fun i j ↦ f (x j - x i))

/-- Uniform boundedness on the real axis. -/
def BoundedOnReal (f : ℝ → ℂ) : Prop :=
  ∃ C : ℝ, ∀ t : ℝ, ‖f t‖ ≤ C

/-- Every displacement in the finite window vanishes. -/
def OnCriticalLine {n : ℕ} (window : FinitePoissonWindow n) : Prop :=
  ∀ i, window.displacement i = 0

@[simp]
theorem phase_zero {n : ℕ} (window : FinitePoissonWindow n) (i : Fin n) :
    phase window 0 i = 1 := by
  simp [phase]

@[simp]
theorem phase_norm {n : ℕ} (window : FinitePoissonWindow n) (t : ℝ) (i : Fin n) :
    ‖phase window t i‖ = 1 := by
  simp [phase, Complex.norm_exp]

theorem phase_sub {n : ℕ} (window : FinitePoissonWindow n) (s t : ℝ) (i : Fin n) :
    star (phase window s i) * phase window t i = phase window (t - s) i := by
  change conj (Complex.exp ((window.ordinate i * s : ℝ) * Complex.I)) *
      Complex.exp ((window.ordinate i * t : ℝ) * Complex.I) =
    Complex.exp ((window.ordinate i * (t - s) : ℝ) * Complex.I)
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, conj_ofReal, conj_I]
  push_cast
  ring

@[simp]
theorem inversePoissonSum_zero {n : ℕ} (window : FinitePoissonWindow n) :
    inversePoissonSum window 0 = n := by
  simp [inversePoissonSum]

theorem inversePoissonSum_eq_phase_sum_of_critical {n : ℕ}
    (window : FinitePoissonWindow n) (hCritical : OnCriticalLine window) (t : ℝ) :
    inversePoissonSum window t = ∑ i, phase window t i := by
  apply Finset.sum_congr rfl
  intro i _
  simp [hCritical i]

/-- Critical-line windows give Gram kernels of their finite character family. -/
theorem positiveDefinite_of_critical {n : ℕ} (window : FinitePoissonWindow n)
    (hCritical : OnCriticalLine window) :
    PositiveDefinite (inversePoissonSum window) := by
  intro m x
  let A : Matrix (Fin n) (Fin m) ℂ := fun k i ↦ phase window (x i) k
  have hKernel :
      (fun i j : Fin m ↦ inversePoissonSum window (x j - x i)) = Aᴴ * A := by
    ext i j
    rw [inversePoissonSum_eq_phase_sum_of_critical window hCritical]
    simp only [Matrix.mul_apply, conjTranspose_apply, A]
    exact Finset.sum_congr rfl fun k _ ↦ (phase_sub window (x i) (x j) k).symm
  rw [hKernel]
  exact Matrix.posSemidef_conjTranspose_mul_self A

/-- Positive definiteness supplies the sharp finite-window bound `n`. -/
theorem boundedOnReal_of_positiveDefinite {n : ℕ} (window : FinitePoissonWindow n)
    (hPositive : PositiveDefinite (inversePoissonSum window)) :
    BoundedOnReal (inversePoissonSum window) := by
  refine ⟨n, fun t ↦ ?_⟩
  let x : Fin 2 → ℝ := ![0, t]
  let M : Matrix (Fin 2) (Fin 2) ℂ :=
    fun i j ↦ inversePoissonSum window (x j - x i)
  have hM : M.PosSemidef := hPositive 2 x
  have hSym : inversePoissonSum window (-t) =
      star (inversePoissonSum window t) := by
    have hEntry := hM.isHermitian.apply (0 : Fin 2) (1 : Fin 2)
    simpa [M, x] using congrArg star hEntry
  have hDet := hM.det_nonneg
  have hSquare : ‖inversePoissonSum window t‖ ^ 2 ≤ (n : ℝ) ^ 2 := by
    rw [Matrix.det_fin_two] at hDet
    simp [M, x, inversePoissonSum_zero, hSym] at hDet
    have hNormSq :
        (Complex.normSq (inversePoissonSum window t) : ℂ) ≤
          (((n : ℝ) * n : ℝ) : ℂ) := by
      calc
        (Complex.normSq (inversePoissonSum window t) : ℂ) =
            inversePoissonSum window t * conj (inversePoissonSum window t) :=
          (Complex.mul_conj _).symm
        _ ≤ (n : ℂ) * n := by simpa only [starRingEnd_apply] using hDet
        _ = (((n : ℝ) * n : ℝ) : ℂ) := by norm_cast
    simpa [Complex.normSq_eq_norm_sq, pow_two] using Complex.real_le_real.mp hNormSq
  exact (sq_le_sq₀ (norm_nonneg _) (Nat.cast_nonneg _)).mp hSquare

/-- A finite family of real frequencies has arbitrarily late simultaneous
returns of all its complex phases to one. -/
theorem finite_phase_recurrence {n : ℕ} (gamma : Fin n → ℝ) :
    ∃ tau : ℕ → ℕ,
      Tendsto tau atTop atTop ∧
      ∀ i, Tendsto
        (fun k ↦ Complex.exp ((gamma i * (tau k : ℝ) : ℝ) * Complex.I))
        atTop (𝓝 1) := by
  let u : ℕ → (Fin n → ℂ) := fun m i ↦
    Complex.exp ((gamma i * (m : ℝ) : ℝ) * Complex.I)
  have huBall : ∀ m, u m ∈ closedBall (0 : Fin n → ℂ) 1 := by
    intro m
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    simp [u, Complex.norm_exp]
  obtain ⟨a, _ha, phi, hphi, hlim⟩ :=
    tendsto_subseq_of_bounded (s := closedBall (0 : Fin n → ℂ) 1)
      Metric.isBounded_closedBall huBall
  let tau : ℕ → ℕ := fun k ↦ phi (k + k) - phi k
  have htau : Tendsto tau atTop atTop := by
    apply tendsto_atTop_mono (fun k ↦ ?_) tendsto_id
    dsimp [tau]
    exact Nat.le_sub_of_add_le (hphi.add_le_nat k k)
  refine ⟨tau, htau, fun i ↦ ?_⟩
  have hsmall : Tendsto (fun k ↦ u (phi k) i) atTop (𝓝 (a i)) := by
    simpa [Function.comp_def] using tendsto_pi_nhds.mp hlim i
  have hdouble : Tendsto (fun k ↦ u (phi (k + k)) i) atTop (𝓝 (a i)) := by
    apply hsmall.comp
    exact tendsto_atTop_mono (fun k ↦ Nat.le_add_right k k) tendsto_id
  have haNorm : ‖a i‖ = 1 := by
    apply tendsto_nhds_unique (hsmall.norm)
    simpa [u, Complex.norm_exp] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
  have hProduct : Tendsto
      (fun k ↦ u (phi (k + k)) i * (starRingEnd ℂ) (u (phi k) i))
      atTop (𝓝 1) := by
    have hLimit : a i * (starRingEnd ℂ) (a i) = 1 := by
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, haNorm]
      norm_num
    simpa only [Function.comp_apply, hLimit] using
      hdouble.mul (Complex.continuous_conj.continuousAt.tendsto.comp hsmall)
  apply hProduct.congr'
  filter_upwards with k
  have hle : phi k ≤ phi (k + k) := hphi.monotone (Nat.le_add_right k k)
  dsimp [u, tau]
  change Complex.exp ((gamma i * (phi (k + k) : ℝ) : ℝ) * Complex.I) *
      conj (Complex.exp ((gamma i * (phi k : ℝ) : ℝ) * Complex.I)) =
    Complex.exp ((gamma i * ((phi (k + k) - phi k : ℕ) : ℝ) : ℝ) * Complex.I)
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, conj_ofReal, conj_I]
  push_cast [Nat.cast_sub hle]
  ring

/-- At nonnegative times, normalization by a candidate maximal growth rate
distributes across the finite inverse-Poisson sum. -/
theorem normalized_inversePoissonSum {n : ℕ} (window : FinitePoissonWindow n)
    (r t : ℝ) (ht : 0 ≤ t) :
    (Real.exp (-r * t) : ℂ) * inversePoissonSum window t =
      ∑ i, (Real.exp ((-window.displacement i - r) * t) : ℂ) *
        phase window t i := by
  rw [inversePoissonSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [abs_of_nonneg ht, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  push_cast
  congr 2
  ring

/-- Under the functional-equation pairing, boundedness excludes every nonzero
displacement. The maximum-growth trigonometric polynomial cannot cancel: the
preceding recurrence lemma makes all of its phases return to one together. -/
theorem critical_of_boundedOnReal {n : ℕ} (window : FinitePoissonWindow n)
    (hBounded : BoundedOnReal (inversePoissonSum window)) :
    OnCriticalLine window := by
  intro i
  by_contra hi
  have hFinNonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨i, Finset.mem_univ i⟩
  obtain ⟨imax, _himax, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n))
      (fun j ↦ -window.displacement j) hFinNonempty
  let r : ℝ := -window.displacement imax
  have hrate : ∀ j, -window.displacement j ≤ r := fun j ↦
    hmax j (Finset.mem_univ j)
  have hNegative : ∃ j, window.displacement j < 0 := by
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · exact ⟨i, hneg⟩
    · refine ⟨window.reflect i, ?_⟩
      rw [window.displacement_reflect]
      linarith
  have hrPositive : 0 < r := by
    obtain ⟨j, hj⟩ := hNegative
    exact lt_of_lt_of_le (neg_pos.mpr hj) (hrate j)
  obtain ⟨tau, htau, hphase⟩ := finite_phase_recurrence window.ordinate
  have htauReal : Tendsto (fun k ↦ (tau k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp htau
  let dominant : Finset (Fin n) :=
    Finset.univ.filter fun j ↦ -window.displacement j = r
  have himaxDominant : imax ∈ dominant := by
    simp [dominant, r]
  have hTerm : ∀ j, Tendsto
      (fun k ↦
        (Real.exp ((-window.displacement j - r) * (tau k : ℝ)) : ℂ) *
          phase window (tau k : ℝ) j)
      atTop (𝓝 (if -window.displacement j = r then 1 else 0)) := by
    intro j
    by_cases hj : -window.displacement j = r
    · simp only [hj, sub_self, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]
      simpa [phase] using hphase j
    · have hjlt : -window.displacement j - r < 0 := sub_neg.mpr <|
        lt_of_le_of_ne (hrate j) hj
      have hDecayReal : Tendsto
          (fun k ↦ Real.exp ((-window.displacement j - r) * (tau k : ℝ)))
          atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp
          (htauReal.const_mul_atTop_of_neg hjlt)
      have hDecay : Tendsto
          (fun k ↦
            (Real.exp ((-window.displacement j - r) * (tau k : ℝ)) : ℂ))
          atTop (𝓝 0) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp hDecayReal
      have hPhase : Tendsto (fun k ↦ phase window (tau k : ℝ) j) atTop (𝓝 1) := by
        simpa only [phase] using hphase j
      simpa only [if_neg hj, zero_mul] using hDecay.mul hPhase
  have hExpanded : Tendsto
      (fun k ↦ ∑ j,
        (Real.exp ((-window.displacement j - r) * (tau k : ℝ)) : ℂ) *
          phase window (tau k : ℝ) j)
      atTop (𝓝 (dominant.card : ℂ)) := by
    have hSum := tendsto_finsetSum Finset.univ fun j _ ↦ hTerm j
    simpa [dominant] using hSum
  have hNormalized : Tendsto
      (fun k ↦ (Real.exp (-r * (tau k : ℝ)) : ℂ) *
        inversePoissonSum window (tau k : ℝ))
      atTop (𝓝 (dominant.card : ℂ)) := by
    apply hExpanded.congr'
    filter_upwards with k
    exact (normalized_inversePoissonSum window r (tau k : ℝ)
      (Nat.cast_nonneg _)).symm
  obtain ⟨C, hC⟩ := hBounded
  have hDecayReal : Tendsto (fun k ↦ Real.exp (-r * (tau k : ℝ)))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (htauReal.const_mul_atTop_of_neg (neg_lt_zero.mpr hrPositive))
  have hDecay : Tendsto (fun k ↦ (Real.exp (-r * (tau k : ℝ)) : ℂ))
      atTop (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hDecayReal
  have hQBounded : IsBoundedUnder (· ≤ ·) atTop
      (norm ∘ fun k ↦ inversePoissonSum window (tau k : ℝ)) :=
    isBoundedUnder_of_eventually_le <| Eventually.of_forall fun k ↦ hC _
  have hNormalizedZero : Tendsto
      (fun k ↦ (Real.exp (-r * (tau k : ℝ)) : ℂ) *
        inversePoissonSum window (tau k : ℝ))
      atTop (𝓝 0) :=
    hDecay.zero_mul_isBoundedUnder_le hQBounded
  have hCardZero : (dominant.card : ℂ) = 0 :=
    tendsto_nhds_unique hNormalized hNormalizedZero
  have hCardPositive : 0 < dominant.card := Finset.card_pos.mpr ⟨imax, himaxDominant⟩
  exact hCardPositive.ne' (Nat.cast_eq_zero.mp (Complex.ofReal_eq_zero.mp hCardZero))

/-- Finite-window inverse-Poisson RH criterion. The window is reflected at
fixed ordinate, exactly encoding the functional-equation pair used to turn an
off-line zero into a positive growth rate. -/
theorem finite_inverse_poisson_rh_criterion {n : ℕ}
    (window : FinitePoissonWindow n) :
    OnCriticalLine window ↔
      PositiveDefinite (inversePoissonSum window) ∧
      BoundedOnReal (inversePoissonSum window) := by
  constructor
  · intro hCritical
    have hPositive := positiveDefinite_of_critical window hCritical
    exact ⟨hPositive, boundedOnReal_of_positiveDefinite window hPositive⟩
  · exact fun h ↦ critical_of_boundedOnReal window h.2

/-- The empty window checks the intended degenerate case: its inverse-Poisson
sum is zero and all three criterion conditions hold. -/
theorem empty_window_example :
    ∃ window : FinitePoissonWindow 0,
      OnCriticalLine window ∧
      PositiveDefinite (inversePoissonSum window) ∧
      BoundedOnReal (inversePoissonSum window) := by
  let window : FinitePoissonWindow 0 :=
    { displacement := fun i ↦ Fin.elim0 i
      ordinate := fun i ↦ Fin.elim0 i
      reflect := Equiv.refl _
      displacement_reflect := by
        intro i
        exact Fin.elim0 i
      ordinate_reflect := by
        intro i
        exact Fin.elim0 i }
  exact ⟨window, fun i ↦ Fin.elim0 i,
    (finite_inverse_poisson_rh_criterion window).mp (fun i ↦ Fin.elim0 i)⟩

/-- A reflected two-point off-line window is a concrete unbounded witness. -/
def offLinePairWindow : FinitePoissonWindow 2 where
  displacement := ![-1, 1]
  ordinate := ![0, 0]
  reflect := Equiv.swap 0 1
  displacement_reflect := by
    intro i
    fin_cases i <;> norm_num
  ordinate_reflect := by
    intro i
    fin_cases i <;> norm_num

theorem offLinePairWindow_unbounded :
    ¬BoundedOnReal (inversePoissonSum offLinePairWindow) := by
  intro hBounded
  have hCritical := critical_of_boundedOnReal offLinePairWindow hBounded
  norm_num [OnCriticalLine, offLinePairWindow] at hCritical

#print axioms positiveDefinite_of_critical
#print axioms boundedOnReal_of_positiveDefinite
#print axioms finite_phase_recurrence
#print axioms critical_of_boundedOnReal
#print axioms finite_inverse_poisson_rh_criterion
#print axioms empty_window_example
#print axioms offLinePairWindow_unbounded

end D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion
