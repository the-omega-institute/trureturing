import D5.S3.Quantum.Divergence.MaximalHockeyStickQuadratic
import D5.S3.Quantum.Divergence.UmegakiRareFlagBKM
import D5.S3.Quantum.Recovery.PetzPositiveTraceFidelity
import D5.S3.Quantum.Recovery.PetzPositiveTracePostselection

/-!
Finite quadratic Bayes risk on an ensemble of subnormalized positive matrices.
The scores are arbitrary reals. The geometric trace deficit bounds the risk
of every finite POVM from below. The supported pretty-good measurement has
exactly twice that deficit, including when the total mass is singular.

The lower bound uses finite square Jensen and two matrix squares. The first
is the Gram square of the commutator with the square root of the total mass.
The second completes the square in the trace form weighted by that root on
both sides. The existing supported inverse suffices for both singular and
faithful ensembles.

This formalizes Section 1 of positive-map-commuting-input-petz-uniform.txt.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Divergence.MaximalHockeyStickQuadratic (square_jensen)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
  (spectralSupport spectralInverseSqrt)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport
  (spectral_sqrt_normalization support_of_nonneg_le_smul)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransformer (spectral_sqrt_inverse_products)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Divergence.LogDerivTrace
  (logDeriv logDeriv_integrable pairKernel_integrable resolvent_eq_spectral)
open D5.S3.Quantum.Divergence.UmegakiRareFlagBKM (pair_kernel_eval trace_cross_spectral)

namespace QuadraticBayesRiskGeometricPetz

variable {n ι κ : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype κ]

/-- The real part of the trace pairing on matrices. -/
def tracePair (A X : Matrix n n ℂ) : ℝ := (trace (A * X)).re

/-- The first matrix moment of a real score on an ensemble or POVM. -/
def scoreMoment (A : ι → Matrix n n ℂ) (c : ι → ℝ) : Matrix n n ℂ :=
  ∑ i, c i • A i

private def scoreSecondMoment (A : ι → Matrix n n ℂ) (c : ι → ℝ) : ℝ :=
  ∑ i, c i ^ 2 * (trace (A i)).re

/-- Actual mean squared loss of the POVM with outcome estimates `y`. -/
def quadraticRisk (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (N : κ → Matrix n n ℂ) (y : κ → ℝ) : ℝ :=
  ∑ i, ∑ j, (c i - y j) ^ 2 * tracePair (A i) (N j)

/-- The geometric trace deficit for the ensemble score. -/
def geometricRisk (A : ι → Matrix n n ℂ) (c : ι → ℝ) : ℝ :=
  let W := spectralInverseSqrt (∑ i, A i)
  let B := scoreMoment A c
  scoreSecondMoment A c - tracePair B (W * B * W)

omit [DecidableEq n] in
private theorem tracePair_comm (A X : Matrix n n ℂ) :
    tracePair A X = tracePair X A :=
  congrArg Complex.re (Matrix.trace_mul_comm A X)

omit [DecidableEq n] in
private theorem tracePair_sum_left (A : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    tracePair (∑ i, A i) X = ∑ i, tracePair (A i) X := by
  simp only [tracePair, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]

omit [DecidableEq n] in
private theorem tracePair_sum_right (A : Matrix n n ℂ) (X : κ → Matrix n n ℂ) :
    tracePair A (∑ j, X j) = ∑ j, tracePair A (X j) := by
  simp only [tracePair, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

omit [DecidableEq n] in
private theorem tracePair_smul_left (r : ℝ) (A X : Matrix n n ℂ) :
    tracePair (r • A) X = r * tracePair A X := by
  simp only [tracePair, Matrix.smul_mul, Matrix.trace_smul, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

omit [DecidableEq n] in
private theorem tracePair_smul_right (r : ℝ) (A X : Matrix n n ℂ) :
    tracePair A (r • X) = r * tracePair A X := by
  rw [tracePair_comm A (r • X), tracePair_smul_left, tracePair_comm X A]

omit [DecidableEq n] in
private theorem tracePair_mono_right {A X Y : Matrix n n ℂ}
    (hA : A.PosSemidef) (hXY : X ≤ Y) : tracePair A X ≤ tracePair A Y := by
  classical
  have h := (Complex.nonneg_iff.mp (hA.trace_mul_nonneg (Matrix.le_iff.mp hXY))).1
  apply sub_nonneg.mp
  simpa only [tracePair, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] using h

omit [Fintype n] [DecidableEq n] in
private theorem scoreMoment_isHermitian (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) : (scoreMoment A c).IsHermitian := by
  unfold scoreMoment
  apply isSelfAdjoint_sum
  intro i _
  exact (hA i).isHermitian.smul (IsSelfAdjoint.all (c i))

omit [Fintype n] [DecidableEq n] in
private theorem ensemble_posSemidef (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) : (∑ i, A i).PosSemidef :=
  Matrix.posSemidef_sum Finset.univ fun i _ => hA i

private theorem ensemble_support (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (i : ι) :
    let P := spectralSupport (∑ j, A j)
    P * A i = A i ∧ A i * P = A i := by
  let Q := ∑ j, A j
  let P := spectralSupport Q
  change P * A i = A i ∧ A i * P = A i
  obtain ⟨-, -, hP, -, -, -, hPQ, -⟩ :=
    spectral_sqrt_normalization Q (ensemble_posSemidef A hA)
  have hle : A i ≤ Q :=
    Finset.single_le_sum (fun j _ => (hA j).nonneg) (Finset.mem_univ i)
  exact support_of_nonneg_le_smul Q (A i) P hP hPQ (hA i) 1
    (by simpa only [one_smul] using hle)

private theorem risk_expansion (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (N : κ → Matrix n n ℂ) (y : κ → ℝ) (hSum : ∑ j, N j = 1) :
    quadraticRisk A c N y = scoreSecondMoment A c -
      2 * tracePair (scoreMoment A c) (scoreMoment N y) +
      tracePair (∑ i, A i) (scoreMoment N (fun j => y j ^ 2)) := by
  have hrow (i : ι) :
      (∑ j, (c i - y j) ^ 2 * tracePair (A i) (N j)) =
        c i ^ 2 * (trace (A i)).re -
          2 * (c i * tracePair (A i) (scoreMoment N y)) +
          tracePair (A i) (scoreMoment N (fun j => y j ^ 2)) := by
    have hmass :
        (∑ j, c i ^ 2 * tracePair (A i) (N j)) = c i ^ 2 * (trace (A i)).re := by
      rw [← Finset.mul_sum, ← tracePair_sum_right, hSum]
      simp only [tracePair, Matrix.mul_one]
    have hfirst :
        (∑ j, 2 * (c i * (y j * tracePair (A i) (N j)))) =
          2 * (c i * tracePair (A i) (scoreMoment N y)) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      simp only [scoreMoment, tracePair_sum_right, tracePair_smul_right]
    have hsecond :
        (∑ j, y j ^ 2 * tracePair (A i) (N j)) =
          tracePair (A i) (scoreMoment N (fun j => y j ^ 2)) := by
      simp only [scoreMoment, tracePair_sum_right, tracePair_smul_right]
    calc
      _ = ∑ j, (c i ^ 2 * tracePair (A i) (N j) -
          2 * (c i * (y j * tracePair (A i) (N j))) +
          y j ^ 2 * tracePair (A i) (N j)) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hmass, hfirst, hsecond]
  have hfirst :
      (∑ i, 2 * (c i * tracePair (A i) (scoreMoment N y))) =
        2 * tracePair (scoreMoment A c) (scoreMoment N y) := by
    rw [← Finset.mul_sum]
    simp only [scoreMoment, tracePair_sum_left, tracePair_smul_left]
  unfold quadraticRisk
  simp_rw [hrow]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hfirst, ← tracePair_sum_left,
    scoreSecondMoment]

/-- The Gram square of the commutator with a Hermitian square root compares
the arithmetic and geometric weights for the quadratic term. -/
private theorem geometric_quadratic_le (Q X R : Matrix n n ℂ)
    (hR : Rᴴ = R) (hRR : R * R = Q) (hX : X.IsHermitian) :
    (trace ((X * R) * (X * R))).re ≤ tracePair Q (X * X) := by
  let D := R * X - X * R
  have h := (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self D).trace_nonneg).1
  have h1 : trace ((X * R) * (R * X)) = trace (Q * (X * X)) := by
    calc
      _ = trace (X * (R * R) * X) := by simp only [Matrix.mul_assoc]
      _ = trace (Q * (X * X)) := by
        rw [hRR, Matrix.trace_mul_cycle X Q X, Matrix.trace_mul_comm (X * X) Q]
  have h2 : trace ((R * X) * (X * R)) = trace (Q * (X * X)) := by
    calc
      _ = trace (R * (X * X) * R) := by simp only [Matrix.mul_assoc]
      _ = trace (Q * (X * X)) := by rw [Matrix.trace_mul_cycle, hRR]
  have h3 : trace ((R * X) * (R * X)) = trace ((X * R) * (X * R)) := by
    calc
      _ = trace (R * (X * (R * X))) := by simp only [Matrix.mul_assoc]
      _ = trace ((X * (R * X)) * R) := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  change 0 ≤ (trace ((R * X - X * R)ᴴ * (R * X - X * R))).re at h
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hR, hX.eq,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, h1, h2, h3] at h
  unfold tracePair
  linarith only [h]

private theorem complete_geometric_square (Q B X : Matrix n n ℂ)
    (hQ : Q.PosSemidef) (hB : B.IsHermitian) (hX : X.IsHermitian)
    (hPB : spectralSupport Q * B = B) (hBP : B * spectralSupport Q = B) :
    2 * tracePair B X ≤ tracePair Q (X * X) +
      tracePair B (spectralInverseSqrt Q * B * spectralInverseSqrt Q) := by
  let R := CFC.sqrt Q
  let W := spectralInverseSqrt Q
  let Y := W * B * W
  change 2 * tracePair B X ≤ tracePair Q (X * X) + tracePair B Y
  obtain ⟨-, hW, -, -, -, -, -, -⟩ := spectral_sqrt_normalization Q hQ
  change Wᴴ = W at hW
  obtain ⟨hRW, hWR, -, -⟩ := spectral_sqrt_inverse_products Q hQ
  have hY : Yᴴ = Y := by
    simp only [Y, Matrix.conjTranspose_mul, hW, hB.eq, Matrix.mul_assoc]
  have hRYR : R * Y * R = B := by
    calc
      _ = (R * W) * B * (W * R) := by simp only [Y, Matrix.mul_assoc]
      _ = _ := by rw [hRW, hWR, hPB, hBP]
  have hcross₁ : trace (X * R * Y * R) = trace (B * X) := by
    calc
      _ = trace (X * (R * Y * R)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hRYR, Matrix.trace_mul_comm X B]
  have hcross₂ : trace (Y * R * X * R) = trace (B * X) := by
    calc
      _ = trace ((Y * R) * (X * R)) := by simp only [Matrix.mul_assoc]
      _ = trace ((X * R) * (Y * R)) := Matrix.trace_mul_comm _ _
      _ = _ := by simpa only [Matrix.mul_assoc] using hcross₁
  have hconst : trace (Y * R * Y * R) = trace (B * Y) := by
    calc
      _ = trace (Y * (R * Y * R)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hRYR, Matrix.trace_mul_comm Y B]
  have hR : R.PosSemidef := (CFC.sqrt_nonneg Q).posSemidef
  have hD : ((X - Y) * R * (X - Y)).PosSemidef := by
    simpa only [Matrix.conjTranspose_sub, hX.eq, hY] using
      hR.conjTranspose_mul_mul_same (X - Y)
  have h := (Complex.nonneg_iff.mp (hD.trace_mul_nonneg hR)).1
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
    hcross₁, hcross₂, hconst] at h
  have hquad := geometric_quadratic_le Q X R hR.isHermitian.eq
    (CFC.sqrt_mul_sqrt_self Q hQ.nonneg) hX
  rw [← Matrix.mul_assoc (X * R) X R] at hquad
  unfold tracePair at hquad ⊢
  linarith only [h, hquad]

/-- Every finite POVM and every real estimator has actual risk at least the
geometric trace deficit. The ensemble can have singular total mass. -/
theorem geometricRisk_le_quadraticRisk (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (N : κ → Matrix n n ℂ) (y : κ → ℝ)
    (hN : ∀ j, (N j).PosSemidef) (hSum : ∑ j, N j = 1) :
    geometricRisk A c ≤ quadraticRisk A c N y := by
  let Q := ∑ i, A i
  let P := spectralSupport Q
  let B := scoreMoment A c
  let X := scoreMoment N y
  have hQ := ensemble_posSemidef A hA
  have hleft (i : ι) : P * A i = A i := (ensemble_support A hA i).1
  have hright (i : ι) : A i * P = A i := (ensemble_support A hA i).2
  have hPB : P * B = B := by
    simp only [B, scoreMoment, Matrix.mul_sum, Matrix.mul_smul, hleft]
  have hBP : B * P = B := by
    simp only [B, scoreMoment, Matrix.sum_mul, Matrix.smul_mul, hright]
  have hJ :
      tracePair Q (X * X) ≤ tracePair Q (scoreMoment N (fun j => y j ^ 2)) :=
    tracePair_mono_right hQ (square_jensen N y hN hSum)
  have hSquare := complete_geometric_square Q B X hQ
    (scoreMoment_isHermitian A c hA) (scoreMoment_isHermitian N y hN) hPB hBP
  rw [risk_expansion A c N y hSum]
  change scoreSecondMoment A c - tracePair B (spectralInverseSqrt Q * B *
      spectralInverseSqrt Q) ≤
    scoreSecondMoment A c - 2 * tracePair B X +
      tracePair Q (scoreMoment N (fun j => y j ^ 2))
  linarith only [hJ, hSquare]

/-- The pretty-good effects, completed by the projection onto the kernel of
the total mass. -/
def pgmEffects (A : ι → Matrix n n ℂ) : Option ι → Matrix n n ℂ
  | none => 1 - spectralSupport (∑ i, A i)
  | some i => spectralInverseSqrt (∑ j, A j) * A i * spectralInverseSqrt (∑ j, A j)

/-- Use the ensemble score on its PGM outcome and zero on the null outcome. -/
def pgmScores (c : ι → ℝ) : Option ι → ℝ
  | none => 0
  | some i => c i

theorem pgmEffects_isPOVM (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) :
    (∀ j, (pgmEffects A j).PosSemidef) ∧ (∑ j, pgmEffects A j) = 1 := by
  let Q := ∑ i, A i
  let P := spectralSupport Q
  let W := spectralInverseSqrt Q
  obtain ⟨-, hW, hP, hPP, -, -, -, hWQW⟩ :=
    spectral_sqrt_normalization Q (ensemble_posSemidef A hA)
  change Wᴴ = W at hW
  constructor
  · intro j
    cases j with
    | none =>
      change (1 - P).PosSemidef
      have hProj : IsStarProjection P := ⟨hPP, hP⟩
      exact hProj.one_sub_nonneg.posSemidef
    | some i =>
      change (W * A i * W).PosSemidef
      simpa only [hW] using (hA i).conjTranspose_mul_mul_same W
  · rw [Fintype.sum_option]
    change 1 - P + (∑ i, W * A i * W) = 1
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, hWQW, sub_add_cancel]

private theorem pgm_mass (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (j : ι) :
    tracePair (∑ i, A i) (pgmEffects A (some j)) = (trace (A j)).re := by
  let Q := ∑ i, A i
  let W := spectralInverseSqrt Q
  obtain ⟨-, -, -, -, -, -, -, hWQW⟩ :=
    spectral_sqrt_normalization Q (ensemble_posSemidef A hA)
  unfold tracePair
  apply congrArg Complex.re
  change trace (Q * (W * A j * W)) = trace (A j)
  calc
    _ = trace ((Q * W * A j) * W) := by simp only [Matrix.mul_assoc]
    _ = trace (W * (Q * W * A j)) := Matrix.trace_mul_comm _ _
    _ = trace ((W * Q * W) * A j) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hWQW, (ensemble_support A hA j).1]

/-- The actual PGM risk is exactly twice the geometric trace deficit. -/
theorem pgm_quadraticRisk_eq (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) :
    quadraticRisk A c (pgmEffects A) (pgmScores c) = 2 * geometricRisk A c := by
  let Q := ∑ i, A i
  let W := spectralInverseSqrt Q
  have hfirst :
      scoreMoment (pgmEffects A) (pgmScores c) = W * scoreMoment A c * W := by
    unfold scoreMoment
    rw [Fintype.sum_option]
    simp only [pgmEffects, pgmScores, zero_smul, zero_add, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul, W, Q]
  have hsecond :
      tracePair Q (scoreMoment (pgmEffects A) (fun j => pgmScores c j ^ 2)) =
        scoreSecondMoment A c := by
    unfold scoreMoment
    rw [tracePair_sum_right, Fintype.sum_option]
    simp only [tracePair_smul_right, pgmScores, zero_pow (by decide : 2 ≠ 0), zero_mul,
      zero_add, Q, pgm_mass A hA, scoreSecondMoment]
  rw [risk_expansion A c (pgmEffects A) (pgmScores c) (pgmEffects_isPOVM A hA).2, hfirst]
  change scoreSecondMoment A c - 2 * tracePair (scoreMoment A c) (W * scoreMoment A c * W) +
      tracePair Q (scoreMoment (pgmEffects A) (fun j => pgmScores c j ^ 2)) =
    2 * (scoreSecondMoment A c - tracePair (scoreMoment A c) (W * scoreMoment A c * W))
  rw [hsecond]
  ring

/-- Pairwise form of the geometric deficit, with half the ordered double
sum so that the label type needs only a finite enumeration. -/
theorem geometricRisk_eq_half_pairwise (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) :
    geometricRisk A c = (1 / 2) * ∑ i, ∑ j, (c i - c j) ^ 2 *
      tracePair (A i) (pgmEffects A (some j)) := by
  have hNull (i : ι) : tracePair (A i) (pgmEffects A none) = 0 := by
    simp only [pgmEffects, tracePair, Matrix.mul_sub, Matrix.mul_one,
      (ensemble_support A hA i).2, sub_self, Matrix.trace_zero, Complex.zero_re]
  have hRisk : quadraticRisk A c (pgmEffects A) (pgmScores c) =
      ∑ i, ∑ j, (c i - c j) ^ 2 * tracePair (A i) (pgmEffects A (some j)) := by
    unfold quadraticRisk
    apply Finset.sum_congr rfl
    intro i _
    rw [Fintype.sum_option]
    simp only [hNull, mul_zero, zero_add, pgmScores]
  rw [← hRisk, pgm_quadraticRisk_eq A c hA]
  ring

omit [DecidableEq n] in
/-- Pointwise Loewner domination scales actual risk for each fixed finite
measurement and score vector. -/
theorem smul_quadraticRisk_le (A A' : ι → Matrix n n ℂ) (c : ι → ℝ)
    (N : κ → Matrix n n ℂ) (y : κ → ℝ) (hN : ∀ j, (N j).PosSemidef)
    (r : ℝ) (hDom : ∀ i, r • A i ≤ A' i) :
    r * quadraticRisk A c N y ≤ quadraticRisk A' c N y := by
  simp only [quadraticRisk, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h := tracePair_mono_right (hN j) (hDom i)
  rw [tracePair_comm (N j) (r • A i), tracePair_comm (N j) (A' i),
    tracePair_smul_left] at h
  calc
    _ = (c i - y j) ^ 2 * (r * tracePair (A i) (N j)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- Loewner domination transfers geometric deficits through actual finite
quadratic risk. This applies with the score chosen separately at each point
of an ensemble path. -/
theorem smul_geometricRisk_le_two (A A' : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hA' : ∀ i, (A' i).PosSemidef)
    (r : ℝ) (hr : 0 ≤ r) (hDom : ∀ i, r • A i ≤ A' i) :
    r * geometricRisk A c ≤ 2 * geometricRisk A' c := by
  let N := pgmEffects A'
  let y := pgmScores c
  obtain ⟨hN, hSum⟩ := pgmEffects_isPOVM A' hA'
  calc
    _ ≤ r * quadraticRisk A c N y :=
      mul_le_mul_of_nonneg_left (geometricRisk_le_quadraticRisk A c hA N y hN hSum) hr
    _ ≤ quadraticRisk A' c N y := smul_quadraticRisk_le A A' c N y hN r hDom
    _ = _ := pgm_quadraticRisk_eq A' c hA'

section PositiveMap

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The actual trace dual pulls back a retained POVM and preserves the
quadratic risk on the corresponding ensembles. -/
theorem quadraticRisk_traceDual (Φ : MatrixMap n m ℂ) (hΦ : Φ.IsPositive)
    (hTP : ∀ X, trace (Φ X) = trace X)
    (A : ι → Matrix n n ℂ) (c : ι → ℝ) (N : κ → Matrix m m ℂ) (y : κ → ℝ)
    (hN : ∀ j, (N j).PosSemidef) (hSum : ∑ j, N j = 1) :
    (∀ j, (Φ.dual (N j)).PosSemidef) ∧ (∑ j, Φ.dual (N j)) = 1 ∧
      quadraticRisk A c (fun j => Φ.dual (N j)) y =
        quadraticRisk (fun i => Φ (A i)) c N y := by
  refine ⟨fun j => hΦ.dual (hN j), ?_, ?_⟩
  · rw [← map_sum, hSum, PetzPositiveTraceFidelity.traceDual_unital Φ hTP]
  · simp only [quadraticRisk, tracePair, ← MatrixMap.Dual.trace_eq]

/-- For a reference slice `S * K * S = A j`, with `S = sqrt σ`, the
ordinary Petz readout is the corresponding score moment of the retained
PGM transition masses. The formula also applies to singular references. -/
theorem ordinaryPetz_slice_trace_eq (Φ : MatrixMap n m ℂ)
    (σ K : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (c : ι → ℝ) (j : ι)
    (hSum : ∑ i, A i = σ) (hSlice : CFC.sqrt σ * K * CFC.sqrt σ = A j) :
    tracePair K (PetzPositiveTracePostselection.ordinaryPetz Φ σ
      (Φ (scoreMoment A c))) =
      ∑ i, c i * tracePair (Φ (A j)) (pgmEffects (fun k => Φ (A k)) (some i)) := by
  let S := CFC.sqrt σ
  let W := spectralInverseSqrt (Φ σ)
  let M := W * Φ (scoreMoment A c) * W
  have hRetained : (∑ i, Φ (A i)) = Φ σ := by rw [← map_sum, hSum]
  have hMoment : Φ (scoreMoment A c) = ∑ i, c i • Φ (A i) := by
    rw [scoreMoment, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact LinearMap.map_smul_of_tower Φ (c i) (A i)
  have hTrace : trace (K * (S * Φ.dual M * S)) = trace (Φ (A j) * M) := by
    calc
      _ = trace (S * K * (S * Φ.dual M)) := by
        rw [← Matrix.mul_assoc K (S * Φ.dual M) S, Matrix.trace_mul_cycle]
      _ = trace ((S * K * S) * Φ.dual M) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hSlice, ← MatrixMap.Dual.trace_eq]
  calc
    _ = tracePair (Φ (A j)) M := congrArg Complex.re hTrace
    _ = _ := by
      simp only [M, hMoment, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
        tracePair_sum_right, tracePair_smul_right, pgmEffects, hRetained, W]

end PositiveMap

private theorem pair_kernel_le_geometric (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Set.Ioi (0 : ℝ), 1 / ((a + t) * (b + t))) ≤
      (Real.sqrt a)⁻¹ * (Real.sqrt b)⁻¹ := by
  let g := Real.sqrt a * Real.sqrt b
  have hg : 0 < g := mul_pos (Real.sqrt_pos.2 ha) (Real.sqrt_pos.2 hb)
  have hsum : 2 * g ≤ a + b := by
    dsimp [g]
    nlinarith only [sq_nonneg (Real.sqrt a - Real.sqrt b),
      Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
  have hprod : g ^ 2 = a * b := by
    dsimp [g]
    rw [mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
  calc
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), 1 / ((g + t) * (g + t)) := by
      apply integral_mono_ae (pairKernel_integrable a b ha hb)
        (pairKernel_integrable g g hg hg)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hgt : 0 < g + t := add_pos hg ht
      apply one_div_le_one_div_of_le (mul_pos hgt hgt)
      have hlin := mul_nonneg ht.le (sub_nonneg.mpr hsum)
      nlinarith only [hprod, hlin]
    _ = _ := by
      rw [pair_kernel_eval g g hg hg, ite_eq_left rfl]
      simp [g, one_div, mul_comm]

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
/-- The BKM quadratic form is bounded by the geometric trace form. This
uses the existing logarithmic derivative on positive definite matrices. -/
theorem logDeriv_le_geometric (Q H : Matrix n n ℂ) (hQ : Q.PosDef) (hH : H.IsHermitian) :
    let W := spectralInverseSqrt Q
    tracePair H (logDeriv Q H) ≤ tracePair H (W * H * W) := by
  let U : Matrix n n ℂ := hQ.isHermitian.eigenvectorUnitary
  let q := hQ.isHermitian.eigenvalues
  let Y := Uᴴ * H * U
  let D (d : n → ℝ) : Matrix n n ℂ :=
    U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ
  have hDiag (d : n → ℝ) :
      tracePair H (D d * H * D d) =
        ∑ i, ∑ j, (d i * d j) * Complex.normSq (Y i j) := by
    have h := congrArg Complex.re
      (trace_cross_spectral H U U (fun i => (d i : ℂ)) (fun j => (d j : ℂ)))
    simpa only [tracePair, D, Y, hH.eq, ← Matrix.mul_assoc, Complex.re_sum,
      ← Complex.ofReal_mul, Complex.ofReal_re] using h
  have hW : spectralInverseSqrt Q = D (fun i => (Real.sqrt (q i))⁻¹) := by
    unfold spectralInverseSqrt
    rw [hQ.isHermitian.cfc_eq]
    simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Function.comp_def,
      RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose, D, U, q]
  let f : ℝ → Matrix n n ℂ := fun t => (Q + t • 1)⁻¹ * H * (Q + t • 1)⁻¹
  let T : Matrix n n ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp ((Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap.comp
      (mulLeftLinearMap n ℝ H).toContinuousLinearMap)
  let k (i j : n) (t : ℝ) := (1 / ((q i + t) * (q j + t))) * Complex.normSq (Y i j)
  have hf : Integrable f (volume.restrict (Set.Ioi (0 : ℝ))) := logDeriv_integrable Q H hQ
  have hk (i j : n) : Integrable (k i j) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (pairKernel_integrable _ _ (hQ.eigenvalues_pos i) (hQ.eigenvalues_pos j)).mul_const _
  have hpoint (t : ℝ) (ht : 0 < t) : T (f t) = ∑ i, ∑ j, k i j t := by
    change tracePair H ((Q + t • 1)⁻¹ * H * (Q + t • 1)⁻¹) = _
    rw [resolvent_eq_spectral Q hQ t ht.le]
    simpa only [D, U, q, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Complex.ofReal_inv, k, one_div, mul_inv] using
      hDiag (fun i => (q i + t)⁻¹)
  change tracePair H (logDeriv Q H) ≤
    tracePair H (spectralInverseSqrt Q * H * spectralInverseSqrt Q)
  rw [hW, hDiag]
  calc
    _ = ∫ t in Set.Ioi (0 : ℝ), T (f t) := (T.integral_comp_comm hf).symm
    _ = ∫ t in Set.Ioi (0 : ℝ), ∑ i, ∑ j, k i j t := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hpoint t ht
    _ = ∑ i, ∑ j, (∫ t in Set.Ioi (0 : ℝ), 1 / ((q i + t) * (q j + t))) *
        Complex.normSq (Y i j) := by
      rw [integral_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ (fun j _ => hk i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun j _ => hk i j)]
      apply Finset.sum_congr rfl
      intro j _
      simp only [k, integral_mul_const]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right
        (pair_kernel_le_geometric (q i) (q j) (hQ.eigenvalues_pos i) (hQ.eigenvalues_pos j))
        (Complex.normSq_nonneg _)

/-- The difference between the classical score energy and its retained
BKM form bounds the geometric deficit of the same ensemble and score. -/
theorem geometricRisk_le_bkm_deficit (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hQ : (∑ i, A i).PosDef) :
    geometricRisk A c ≤
      (∑ i, c i ^ 2 * (trace (A i)).re) -
        tracePair (scoreMoment A c) (logDeriv (∑ i, A i) (scoreMoment A c)) := by
  exact sub_le_sub_left
    (logDeriv_le_geometric _ _ hQ (scoreMoment_isHermitian A c hA)) _

end QuadraticBayesRiskGeometricPetz
