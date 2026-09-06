/- GID: D5/S3/Observer/Hankel/DiscreteSteinCompressionStability
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/DiscreteSteinCompressionStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive diagonal discrete Stein dissipation and full observation exclude unit-circle poles after actual principal truncation. -/

import D5.S3.Observer.Hankel.BalancedTruncationTail
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Complex.Norm

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.DiscreteSteinCompressionStability

open Matrix
open D5.S3.Observer.Hankel.BalancedSteinEnergy
open D5.S3.Observer.Hankel.BalancedTruncationTail
open scoped BigOperators

variable {n r m p : ℕ}

/-- The standard complexification of a real matrix. Complex poles, including
nonreal conjugate pairs, are tested rather than only real eigenvalues. -/
def complexMatrix (M : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℂ :=
  M.map (fun t : ℝ => (t : ℂ))

theorem complexMatrix_mul (M : Matrix (Fin m) (Fin n) ℝ)
    (N : Matrix (Fin n) (Fin p) ℝ) :
    complexMatrix (M * N) = complexMatrix M * complexMatrix N := by
  ext i j
  simp [complexMatrix, Matrix.mul_apply]

private theorem action_re (M : Matrix (Fin m) (Fin n) ℝ) (z : Fin n → ℂ) :
    (fun i => ((complexMatrix M).mulVec z i).re) = M.mulVec (fun i => (z i).re) := by
  ext i
  simp [complexMatrix, Matrix.mulVec, dotProduct, Complex.mul_re]

private theorem action_im (M : Matrix (Fin m) (Fin n) ℝ) (z : Fin n → ℂ) :
    (fun i => ((complexMatrix M).mulVec z i).im) = M.mulVec (fun i => (z i).im) := by
  ext i
  simp [complexMatrix, Matrix.mulVec, dotProduct, Complex.mul_im]

/-- Positive weighted squared modulus on the complexified state space. -/
def complexEnergy (w : Fin n → ℝ) (z : Fin n → ℂ) : ℝ :=
  ∑ i, w i * Complex.normSq (z i)

theorem complexEnergy_nonneg (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (z : Fin n → ℂ) :
    0 ≤ complexEnergy w z :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (Complex.normSq_nonneg _))

theorem complexEnergy_eq_zero_iff (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (z : Fin n → ℂ) :
    complexEnergy w z = 0 ↔ z = 0 := by
  constructor
  · intro he
    have hh := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        mul_nonneg (le_of_lt (hw i)) (Complex.normSq_nonneg (z i)))).mp he
    ext i
    have hz := (mul_eq_zero.mp (hh i (Finset.mem_univ i))).resolve_left (ne_of_gt (hw i))
    simpa only [Complex.normSq_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] using hz
  · rintro rfl
    simp [complexEnergy]

theorem complexEnergy_pos (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (z : Fin n → ℂ) (hz : z ≠ 0) : 0 < complexEnergy w z := by
  have hn := complexEnergy_nonneg w (fun i => (hw i).le) z
  have hne : complexEnergy w z ≠ 0 := (complexEnergy_eq_zero_iff w hw z).not.mpr hz
  by_contra! hle
  exact hne (le_antisymm hle hn)

theorem complexEnergy_smul (w : Fin n → ℝ) (a : ℂ) (z : Fin n → ℂ) :
    complexEnergy w (a • z) = ‖a‖ ^ 2 * complexEnergy w z := by
  simp only [complexEnergy, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
    Complex.normSq_eq_norm_sq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem energy_parts (w : Fin n → ℝ) (z : Fin n → ℂ) :
    complexEnergy w z = energy w (fun i => (z i).re) + energy w (fun i => (z i).im) := by
  simp [complexEnergy, energy, Complex.normSq_apply, pow_two, mul_add, Finset.sum_add_distrib]

/-- Extend real Stein dissipation to all complex states by real and imaginary
parts. No positivity or eigenvalue premise for a complexified matrix is assumed. -/
theorem complex_observability_stein (w : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (hO : ObservabilityStein w A C) (z : Fin n → ℂ) :
    complexEnergy w ((complexMatrix A).mulVec z) +
      complexEnergy (fun _ => 1) ((complexMatrix C).mulVec z) ≤ complexEnergy w z := by
  have hre := hO (fun i => (z i).re)
  have him := hO (fun i => (z i).im)
  rw [energy_parts, energy_parts, energy_parts, action_re, action_im, action_re, action_im]
  simp only [energy, one_mul] at *
  change _ ≤ _
  unfold squareSum at hre him
  linarith

/-- Real joint readout injectivity implies complex joint readout injectivity. -/
theorem observable_complexification (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ)
    (hobs : ∀ x : Fin n → ℝ, (∀ k : ℕ, (C * A ^ k).mulVec x = 0) → x = 0)
    (z : Fin n → ℂ) (hz : ∀ k : ℕ, (complexMatrix (C * A ^ k)).mulVec z = 0) : z = 0 := by
  have hre : (fun i => (z i).re) = 0 := by
    apply hobs
    intro k
    have hh := congrArg (fun y : Fin p → ℂ => fun i => (y i).re) (hz k)
    simpa only [action_re, Pi.zero_apply, Complex.zero_re] using hh
  have him : (fun i => (z i).im) = 0 := by
    apply hobs
    intro k
    have hh := congrArg (fun y : Fin p → ℂ => fun i => (y i).im) (hz k)
    simpa only [action_im, Pi.zero_apply, Complex.zero_im] using hh
  ext i
  apply Complex.ext
  · exact congrFun hre i
  · exact congrFun him i

/-- Zero extension of a retained prefix, expressed as a finite sum so the
empty retained space is included without a separate nonempty assumption. -/
def prefixLift (hr : r ≤ n) (z : Fin r → ℂ) : Fin n → ℂ :=
  fun i => ∑ j, if Fin.castLE hr j = i then z j else 0

/-- The orthogonal prefix projection in every positive diagonal metric. -/
def prefixProjection (r : ℕ) (z : Fin n → ℂ) : Fin n → ℂ :=
  fun i => if i.val < r then z i else 0

@[simp] theorem prefixLift_at (hr : r ≤ n) (z : Fin r → ℂ) (j : Fin r) :
    prefixLift hr z (Fin.castLE hr j) = z j := by
  have hinj (k : Fin r) : Fin.castLE hr k = Fin.castLE hr j ↔ k = j := by
    constructor
    · intro hh; exact Fin.ext (congrArg Fin.val hh)
    · rintro rfl; rfl
  simp [prefixLift, hinj]

private theorem prefixLift_outside (hr : r ≤ n) (z : Fin r → ℂ) (i : Fin n)
    (hi : r ≤ i.val) : prefixLift hr z i = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hne : Fin.castLE hr j ≠ i := by
    intro he
    have hj := congrArg Fin.val he
    have := j.isLt
    change j.val = i.val at hj
    omega
  simp [hne]

private theorem prefixLift_smul (hr : r ≤ n) (a : ℂ) (z : Fin r → ℂ) :
    prefixLift hr (a • z) = a • prefixLift hr z := by
  ext i
  simp [prefixLift, Finset.mul_sum, mul_ite]

private theorem lift_restrict (hr : r ≤ n) (z : Fin n → ℂ) :
    prefixLift hr (fun j => z (Fin.castLE hr j)) = prefixProjection r z := by
  ext i
  by_cases hi : i.val < r
  · let j : Fin r := ⟨i.val, hi⟩
    have he : Fin.castLE hr j = i := Fin.ext rfl
    rw [← he, prefixLift_at]
    simp [prefixProjection, j, hi]
  · rw [prefixLift_outside hr _ i (Nat.le_of_not_gt hi)]
    simp [prefixProjection, hi]

/-- Matrix action on zero extension is exactly action by the retained columns. -/
theorem action_prefixLift (M : Matrix (Fin m) (Fin n) ℝ) (hr : r ≤ n) (z : Fin r → ℂ) :
    (complexMatrix M).mulVec (prefixLift hr z) =
      (complexMatrix (M.submatrix id (Fin.castLE hr))).mulVec z := by
  ext i
  simp only [complexMatrix, Matrix.map_apply, Matrix.mulVec, dotProduct,
    prefixLift, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [mul_ite]

/-- The discarded state energy is retained exactly in the projection identity. -/
theorem projection_energy_split (w : Fin n → ℝ) (r : ℕ) (z : Fin n → ℂ) :
    complexEnergy w z = complexEnergy w (prefixProjection r z) +
      complexEnergy w (z - prefixProjection r z) := by
  unfold complexEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < r <;> simp [prefixProjection, hi]

private theorem projection_energy_le (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (r : ℕ) (z : Fin n → ℂ) : complexEnergy w (prefixProjection r z) ≤ complexEnergy w z := by
  have hn := complexEnergy_nonneg w (fun i => (hw i).le) (z - prefixProjection r z)
  rw [projection_energy_split w r z]
  linarith

private theorem projection_eq_of_energy_eq (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (r : ℕ) (z : Fin n → ℂ)
    (he : complexEnergy w z = complexEnergy w (prefixProjection r z)) :
    z = prefixProjection r z := by
  have hz : complexEnergy w (z - prefixProjection r z) = 0 := by
    have hh := projection_energy_split w r z
    linarith
  exact sub_eq_zero.mp ((complexEnergy_eq_zero_iff w hw _).mp hz)

/-- Every complex eigenvalue of every actual principal truncation is strictly
inside the unit disk. The discrete Stein omitted-coordinate square rules out
boundary poles. A singular-value gap and reduced minimality are not assumed. -/
theorem principal_truncation_eigenvalue_lt_one (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin p) (Fin n) ℝ)
    (hO : ObservabilityStein w A C)
    (hobs : ∀ x : Fin n → ℝ, (∀ k : ℕ, (C * A ^ k).mulVec x = 0) → x = 0)
    (hr : r ≤ n) (a : ℂ) (v : Fin r → ℂ) (hv : v ≠ 0)
    (hev : (complexMatrix (prefixA hr A)).mulVec v = a • v) : ‖a‖ < 1 := by
  let x := prefixLift hr v
  let y := (complexMatrix A).mulVec x
  have hx : x ≠ 0 := by
    intro hz
    apply hv
    ext j
    have hh := congrFun hz (Fin.castLE hr j)
    simpa only [x, prefixLift_at, Pi.zero_apply] using hh
  have hp : prefixProjection r y = a • x := by
    rw [← lift_restrict hr y]
    have hh : (fun j => y (Fin.castLE hr j)) =
        (complexMatrix (prefixA hr A)).mulVec v := by
      dsimp only [y, x]
      rw [action_prefixLift A hr v]
      rfl
    rw [hh, hev, prefixLift_smul]
  have hepos := complexEnergy_pos w hw x hx
  have ho := complex_observability_stein w A C hO x
  have hpr := projection_energy_le w hw r y
  rw [hp, complexEnergy_smul] at hpr
  have hout0 := complexEnergy_nonneg (fun _ : Fin p => (1 : ℝ))
    (fun _ => by norm_num) ((complexMatrix C).mulVec x)
  change complexEnergy w y + _ ≤ complexEnergy w x at ho
  have hsq : ‖a‖ ^ 2 ≤ 1 := by nlinarith
  have hle : ‖a‖ ≤ 1 := by nlinarith [norm_nonneg a]
  by_contra! hge
  have ha : ‖a‖ = 1 := le_antisymm hle hge
  have hy : complexEnergy w y = complexEnergy w x := by
    rw [ha] at hpr
    nlinarith
  have hpeq : complexEnergy w y = complexEnergy w (prefixProjection r y) := by
    rw [hy, hp, complexEnergy_smul, ha]
    ring
  have heig : (complexMatrix A).mulVec x = a • x :=
    (projection_eq_of_energy_eq w hw r y hpeq).trans hp
  have hCx : (complexMatrix C).mulVec x = 0 := by
    apply (complexEnergy_eq_zero_iff (fun _ : Fin p => (1 : ℝ)) (fun _ => by norm_num) _).mp
    linarith
  have hpow (k : ℕ) : (complexMatrix (A ^ k)).mulVec x = a ^ k • x := by
    induction k with
    | zero => simp [complexMatrix]
    | succ k ih =>
        rw [pow_succ', complexMatrix_mul, ← mulVec_mulVec, ih,
          Matrix.mulVec_smul, heig, smul_smul, pow_succ]
  have hall (k : ℕ) : (complexMatrix (C * A ^ k)).mulVec x = 0 := by
    rw [complexMatrix_mul, ← mulVec_mulVec, hpow, Matrix.mulVec_smul, hCx, smul_zero]
  exact hx (observable_complexification A C hobs x hall)

/-- Strict internal stability in the standard complex spectrum, with no custom
predicate replacing the spectrum. This includes the zero-dimensional cut. -/
theorem principal_truncation_spectrum_lt_one (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin p) (Fin n) ℝ)
    (hO : ObservabilityStein w A C)
    (hobs : ∀ x : Fin n → ℝ, (∀ k : ℕ, (C * A ^ k).mulVec x = 0) → x = 0)
    (hr : r ≤ n) : ∀ a ∈ spectrum ℂ (complexMatrix (prefixA hr A)), ‖a‖ < 1 := by
  intro a ha
  rw [← Matrix.spectrum_toLpLin 2] at ha
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr ha).exists_hasEigenvector
  apply principal_truncation_eigenvalue_lt_one w hw A C hO hobs hr a (WithLp.ofLp v)
  · intro he
    apply hv.2
    ext i
    exact congrFun he i
  · have he := congrArg WithLp.ofLp hv.apply_eq_smul
    exact he

#print axioms principal_truncation_eigenvalue_lt_one
#print axioms principal_truncation_spectrum_lt_one

end D5.S3.Observer.Hankel.DiscreteSteinCompressionStability
