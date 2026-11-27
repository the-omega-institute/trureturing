/- GID: D5/S3/Quantum/PureState/JointRecordDecoding
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/JointRecordDecoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Diagonal dual bound and attained joint decoding for flat orthogonal phase ensembles. -/

import D5.S3.Quantum.Subentropy.GuessingProbability
import D5.S3.Quantum.PureState.PureStateHandshake

/-!
# Exact joint decoding of independent binary pure records

The square-root measurement for pure geometrically uniform ensembles also follows from
Y. C. Eldar and G. D. Forney Jr., *On Quantum Detection and the Square-Root Measurement*,
arXiv:quant-ph/0005132. Here the upper bound is a diagonal positive-semidefinite
certificate and the attaining measurement is the normalized Walsh basis.
-/

namespace JointRecordDecoding

noncomputable section

open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Subentropy.GuessingProbability
open D5.S3.Quantum.PureState.PureStateHandshake

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem star_mul_eq_normSq (z : ℂ) :
    star z * z = (Complex.normSq z : ℂ) :=
  Complex.normSq_eq_conj_mul_self.symm

private theorem self_dot (v : ι → ℂ) :
    star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i)) : ℝ) := by
  simp only [dotProduct, Pi.star_apply, star_mul_eq_normSq, Complex.ofReal_sum]

/-- The repository density state associated to a normalized amplitude. -/
def pureState (v : ι → ℂ) (hv : star v ⬝ᵥ v = 1) : DensityState ι :=
  ⟨CStarMatrix.ofMatrix (rankOneDensity v),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      (Matrix.posSemidef_vecMulVec_self_star v).nonneg, by
      change trace (rankOneDensity v) = 1
      rwa [rankOneDensity, trace_vecMulVec, dotProduct_comm]⟩

@[simp] theorem pureState_matrix (v : ι → ℂ) (hv : star v ⬝ᵥ v = 1) :
    CStarMatrix.ofMatrix.symm (pureState v hv).1 = rankOneDensity v := rfl

private theorem rankOne_quad (u v : ι → ℂ) :
    star v ⬝ᵥ (rankOneDensity u *ᵥ v) = (Complex.normSq (star u ⬝ᵥ v) : ℂ) := by
  have hconj : star (star u ⬝ᵥ v) = star v ⬝ᵥ u := by
    simp [dotProduct, Pi.star_apply, mul_comm]
  rw [rankOneDensity, vecMulVec_mulVec, dotProduct_smul]
  change (star v ⬝ᵥ u) * (star u ⬝ᵥ v) = _
  rw [← hconj, star_mul_eq_normSq]

/-- The unscaled diagonal dual dominates each rank-one density matrix.
Weighted Cauchy–Schwarz is valid even when some weights vanish. -/
theorem diagonal_sub_rankOne_posSemidef (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i)
    (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    (diagonal (fun i => (((∑ j, t j) * t i : ℝ) : ℂ)) -
      rankOneDensity (fun i => (t i : ℂ) * u i)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply IsHermitian.sub
    · apply Matrix.isHermitian_diagonal_of_self_adjoint
      change star _ = _
      funext i
      simp
    · exact (Matrix.posSemidef_vecMulVec_self_star _).isHermitian
  · intro v
    rw [Matrix.sub_mulVec, dotProduct_sub, rankOne_quad]
    have hdiag :
        star v ⬝ᵥ (diagonal (fun i => (((∑ j, t j) * t i : ℝ) : ℂ)) *ᵥ v) =
          (((∑ j, t j) * ∑ i, t i * Complex.normSq (v i) : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply, mulVec_diagonal, Finset.mul_sum,
        Complex.ofReal_sum, Complex.ofReal_mul]
      exact Finset.sum_congr rfl fun i _ => by
        rw [← star_mul_eq_normSq]
        ring
    rw [hdiag, ← Complex.ofReal_sub, Complex.nonneg_iff]
    refine ⟨sub_nonneg.mpr ?_, by simp⟩
    have htriangle : ‖star (fun i => (t i : ℂ) * u i) ⬝ᵥ v‖ ≤ ∑ i, t i * ‖v i‖ := by
      unfold dotProduct
      refine (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ => ?_)
      simp [Pi.star_apply, norm_mul, hu, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ht i)]
    rw [Complex.normSq_eq_norm_sq]
    calc
      _ ≤ (∑ i, t i * ‖v i‖) ^ 2 := by gcongr
      _ ≤ _ := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => ht i)
        (fun i _ => mul_nonneg (ht i) (Complex.normSq_nonneg _))
        (fun i _ => by rw [Complex.normSq_eq_norm_sq]; nlinarith [sq_nonneg (t i * ‖v i‖)] )

/-- A uniform prior on a finite label space. -/
def uniformPrior (ι : Type*) [Fintype ι] : ι → ℝ :=
  fun _ => (Fintype.card ι : ℝ)⁻¹

/-- Phase-modulated amplitudes with a shared nonnegative coordinate profile. -/
def phaseVector (u : ι → ι → ℂ) (t : ι → ℝ) (j : ι) (i : ι) : ℂ :=
  (t i : ℂ) * u j i

theorem phaseVector_norm (u : ι → ι → ℂ) (t : ι → ℝ)
    (hu : ∀ j i, ‖u j i‖ = 1) (ht : ∑ i, t i ^ 2 = 1) (j : ι) :
    star (phaseVector u t j) ⬝ᵥ phaseVector u t j = 1 := by
  rw [self_dot]
  have hs : ∀ i, Complex.normSq (phaseVector u t j i) = t i ^ 2 := by
    intro i
    simp [phaseVector, Complex.normSq_eq_norm_sq, hu]
  simp [hs, ht]

/-- The normalized phase vectors used as measurement vectors. -/
def phaseBasis (u : ι → ι → ℂ) (j : ι) (i : ι) : ℂ :=
  ((Real.sqrt (Fintype.card ι))⁻¹ : ℝ) * u j i

/-- A rank-one effect for each normalized phase vector. -/
def phaseEffect (u : ι → ι → ℂ) (j : ι) : Matrix ι ι ℂ :=
  rankOneDensity (phaseBasis u j)

theorem phaseEffect_posSemidef (u : ι → ι → ℂ) (j : ι) :
    (phaseEffect u j).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

private theorem phaseBasis_scale_sq :
    ((Real.sqrt (Fintype.card ι))⁻¹ : ℝ) ^ 2 = (Fintype.card ι : ℝ)⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (by positivity)]

private theorem phaseEffect_apply (u : ι → ι → ℂ) (j i l : ι) :
    phaseEffect u j i l = (uniformPrior ι j : ℂ) * (u j i * star (u j l)) := by
  simp only [phaseEffect, rankOneDensity, vecMulVec_apply, Pi.star_apply, phaseBasis,
    star_mul, Complex.star_def, Complex.conj_ofReal]
  unfold uniformPrior
  rw [← phaseBasis_scale_sq (ι := ι), Complex.ofReal_pow, pow_two]
  ring

theorem sum_phaseEffect [Nonempty ι] (u : ι → ι → ℂ)
    (horth : ∀ i l, ∑ j, u j i * star (u j l) =
      if i = l then (Fintype.card ι : ℂ) else 0) :
    (∑ j, phaseEffect u j) = 1 := by
  ext i l
  simp only [Matrix.sum_apply, phaseEffect_apply, uniformPrior, ← Finset.mul_sum, horth,
    Matrix.one_apply]
  split_ifs
  · norm_cast
    exact inv_mul_cancel₀ (by positivity)
  · simp

/-- The normalized phase measurement attains the greatest success over all joint POVMs
for an equally likely flat orthogonal phase ensemble. -/
theorem isGreatest_phase [Nonempty ι] (u : ι → ι → ℂ) (t : ι → ℝ)
    (hu : ∀ j i, ‖u j i‖ = 1)
    (horth : ∀ i l, ∑ j, u j i * star (u j l) =
      if i = l then (Fintype.card ι : ℂ) else 0)
    (ht : ∀ i, 0 ≤ t i) (htnorm : ∑ i, t i ^ 2 = 1) :
    IsGreatest (successProbabilitySet (uniformPrior ι) (fun j => pureState (phaseVector u t j)
      (phaseVector_norm u t hu htnorm j))) ((Fintype.card ι : ℝ)⁻¹ * (∑ i, t i) ^ 2) := by
  let ψ := phaseVector u t
  let ρ := fun j => pureState (ψ j) (phaseVector_norm u t hu htnorm j)
  let D : Matrix ι ι ℂ := diagonal fun i => (((∑ j, t j) * t i : ℝ) : ℂ)
  let p := uniformPrior ι
  let c := (Fintype.card ι : ℝ)⁻¹ * (∑ i, t i) ^ 2
  change IsGreatest (successProbabilitySet p ρ) c
  have hp : ∀ j, 0 ≤ p j := fun _ => by dsimp [p, uniformPrior]; positivity
  have hpsum : ∑ j, p j = 1 := by
    simp [p, uniformPrior, mul_inv_cancel₀ (show (Fintype.card ι : ℝ) ≠ 0 by positivity)]
  have hupper (M : ι → Matrix ι ι ℂ) (hM : ∀ j, (M j).PosSemidef)
      (hsM : ∑ j, M j = 1) : successProbability p ρ M ≤ c := by
    have htrace (j : ι) : (trace (M j * rankOneDensity (ψ j))).re ≤
        (trace (M j * D)).re := by
      have h := RHLinalg.trace_mul_nonneg_of_posSemidef (hM j)
        (diagonal_sub_rankOne_posSemidef t ht (u j) (hu j))
      change 0 ≤ (trace (M j * (D - rankOneDensity (ψ j)))).re at h
      rwa [Matrix.mul_sub, trace_sub, Complex.sub_re, sub_nonneg] at h
    unfold successProbability
    simp only [ρ, pureState_matrix]
    calc
      _ ≤ ∑ j, p j * (trace (M j * D)).re :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (htrace j) (hp j)
      _ = _ := by
        change (∑ j, (Fintype.card ι : ℝ)⁻¹ * (trace (M j * D)).re) = c
        rw [← Finset.mul_sum, ← Complex.re_sum, ← trace_sum, ← Matrix.sum_mul, hsM, one_mul]
        simp [c, D, ← Finset.mul_sum, pow_two]
  have hmem : c ∈ successProbabilitySet p ρ := by
    refine ⟨phaseEffect u, phaseEffect_posSemidef u, sum_phaseEffect u horth, ?_⟩
    have hone (j : ι) : (trace (phaseEffect u j * rankOneDensity (ψ j))).re = c := by
      rw [← (pure_state_handshake (ψ j) (phaseVector_norm u t hu htnorm j) _).2.2,
        phaseEffect, rankOne_quad, Complex.ofReal_re]
      have hdot : star (phaseBasis u j) ⬝ᵥ ψ j =
          (((Real.sqrt (Fintype.card ι))⁻¹ * ∑ i, t i : ℝ) : ℂ) := by
        simp only [phaseBasis, ψ, phaseVector, dotProduct, Pi.star_apply, star_mul,
          Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_sum,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hunit : star (u j i) * u j i = 1 := by
          rw [star_mul_eq_normSq, Complex.normSq_eq_norm_sq, hu]
          norm_num
        change (star (u j i) * (↑(Real.sqrt (Fintype.card ι))⁻¹ : ℂ)) *
          ((t i : ℂ) * u j i) = _
        linear_combination
          ((↑(Real.sqrt (Fintype.card ι))⁻¹ : ℂ) * (t i : ℂ)) * hunit
      rw [hdot, Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_of_nonneg (by
        exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
          (Finset.sum_nonneg fun i _ => ht i)), mul_pow, phaseBasis_scale_sq]
    unfold successProbability
    simp only [ρ, pureState_matrix, hone, ← Finset.sum_mul, hpsum, one_mul]
  have hbound : ∀ a ∈ successProbabilitySet p ρ, a ≤ c := by
    rintro a ⟨M, hM, hsM, rfl⟩
    exact hupper M hM hsM
  exact ⟨hmem, fun {_} ha => hbound _ ha⟩

/-- Exact guessing probability for an equally likely ensemble built from a flat orthogonal
phase matrix and a common coordinate profile. The supremum is over all joint POVMs. -/
theorem pGuess_phase [Nonempty ι] (u : ι → ι → ℂ) (t : ι → ℝ)
    (hu : ∀ j i, ‖u j i‖ = 1)
    (horth : ∀ i l, ∑ j, u j i * star (u j l) =
      if i = l then (Fintype.card ι : ℂ) else 0)
    (ht : ∀ i, 0 ≤ t i) (htnorm : ∑ i, t i ^ 2 = 1) :
    pGuess (uniformPrior ι) (fun j => pureState (phaseVector u t j)
      (phaseVector_norm u t hu htnorm j)) =
      (Fintype.card ι : ℝ)⁻¹ * (∑ i, t i) ^ 2 :=
  (isGreatest_phase u t hu horth ht htnorm).csSup_eq

/-- Binary words index both the labels and Walsh coordinates. -/
abbrev Word (k : ℕ) := Fin k → Bool

def bitPhase (j x : Bool) : ℂ := if j && x then -1 else 1

private theorem bitPhase_norm (j x : Bool) : ‖bitPhase j x‖ = 1 := by
  cases j <;> cases x <;> simp [bitPhase]

/-- The Walsh characters on bit strings, before multiplication by the common normalization. -/
def walsh {k : ℕ} (j x : Word k) : ℂ := ∏ i, bitPhase (j i) (x i)

theorem walsh_norm {k : ℕ} (j x : Word k) : ‖walsh j x‖ = 1 := by
  simp [walsh, norm_prod, bitPhase_norm]

theorem sum_words {R : Type*} [CommSemiring R] {k : ℕ}
    (f : Fin k → Bool → R) : (∑ x : Word k, ∏ i, f i (x i)) = ∏ i, ∑ b, f i b := by
  simpa only [Fintype.piFinset_univ] using Finset.sum_prod_piFinset Finset.univ f

theorem sum_bool {R : Type*} [AddCommMonoid R] (f : Bool → R) :
    ∑ b, f b = f false + f true := by
  simp [Fintype.sum_bool, add_comm]

theorem walsh_orthogonal {k : ℕ} (x y : Word k) :
    ∑ j, walsh j x * star (walsh j y) =
      if x = y then (Fintype.card (Word k) : ℂ) else 0 := by
  classical
  have hbit (b c : Bool) :
      (∑ a, bitPhase a b * star (bitPhase a c)) = if b = c then (2 : ℂ) else 0 := by
    rw [sum_bool]
    cases b <;> cases c <;> norm_num [bitPhase]
  simp only [walsh, star_prod, ← Finset.prod_mul_distrib]
  rw [sum_words (fun i a => bitPhase a (x i) * star (bitPhase a (y i)))]
  simp_rw [hbit]
  split_ifs with h
  · subst y
    simp [Fintype.card_fun]
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra! h'
      exact h (funext h')
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- The two nonnegative amplitudes of the symmetrically phased binary ensemble. -/
def bitWeight (s : ℝ) (x : Bool) : ℝ :=
  if x then Real.sqrt ((1 - s) / 2) else Real.sqrt ((1 + s) / 2)

theorem bitWeight_nonneg (s : ℝ) (x : Bool) : 0 ≤ bitWeight s x := by
  cases x <;> simp only [bitWeight, Bool.false_eq_true, ↓reduceIte] <;> positivity

theorem bitWeight_sq_sum {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∑ x, bitWeight s x ^ 2) = 1 := by
  rw [sum_bool]
  simp only [bitWeight, Bool.false_eq_true, ↓reduceIte]
  rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
  ring

/-- The product Walsh profile with one overlap per coordinate. -/
def coordinateWeight {k : ℕ} (s : Fin k → ℝ) (x : Word k) : ℝ :=
  ∏ i, bitWeight (s i) (x i)

theorem coordinateWeight_nonneg {k : ℕ} (s : Fin k → ℝ) (x : Word k) :
    0 ≤ coordinateWeight s x :=
  Finset.prod_nonneg fun i _ => bitWeight_nonneg (s i) (x i)

theorem coordinateWeight_sq_sum {k : ℕ} {s : Fin k → ℝ}
    (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i ≤ 1) :
    (∑ x : Word k, coordinateWeight s x ^ 2) = 1 := by
  simp only [coordinateWeight, ← Finset.prod_pow]
  rw [sum_words (fun i x => bitWeight (s i) x ^ 2)]
  simp only [bitWeight_sq_sum (hs0 _) (hs1 _), Finset.prod_const_one]

/-- The Walsh profile for equal coordinate overlaps. -/
def wordWeight {k : ℕ} (s : ℝ) (x : Word k) : ℝ := coordinateWeight (fun _ => s) x

theorem wordWeight_nonneg {k : ℕ} (s : ℝ) (x : Word k) : 0 ≤ wordWeight s x :=
  coordinateWeight_nonneg (fun _ => s) x

theorem wordWeight_sq_sum {k : ℕ} {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∑ x : Word k, wordWeight s x ^ 2) = 1 :=
  coordinateWeight_sq_sum (fun _ => hs0) (fun _ => hs1)

private theorem bitWeight_add_sq {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (bitWeight s false + bitWeight s true) ^ 2 = 1 + Real.sqrt (1 - s ^ 2) := by
  have hp : 0 ≤ (1 + s) / 2 := by linarith
  have hm : 0 ≤ (1 - s) / 2 := by linarith
  have hprod : Real.sqrt ((1 + s) / 2) * Real.sqrt ((1 - s) / 2) =
      Real.sqrt (1 - s ^ 2) / 2 := by
    have hrad : 0 ≤ 1 - s ^ 2 := by nlinarith
    rw [← Real.sqrt_mul hp, ← show Real.sqrt (4 : ℝ) = 2 by norm_num,
      ← Real.sqrt_div hrad]
    congr 1
    ring
  simp only [bitWeight, Bool.false_eq_true, ↓reduceIte]
  nlinarith [Real.sq_sqrt hp, Real.sq_sqrt hm, hprod]

/-- The canonical Walsh amplitude for a binary word with coordinate-dependent overlaps. -/
def coordinateRecordVector {k : ℕ} (s : Fin k → ℝ) (j : Word k) : Word k → ℂ :=
  phaseVector walsh (coordinateWeight s) j

theorem coordinateRecordVector_norm {k : ℕ} {s : Fin k → ℝ}
    (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i ≤ 1) (j : Word k) :
    star (coordinateRecordVector s j) ⬝ᵥ coordinateRecordVector s j = 1 :=
  phaseVector_norm walsh (coordinateWeight s) walsh_norm (coordinateWeight_sq_sum hs0 hs1) j

/-- The normalized canonical states with one overlap per coordinate. -/
def coordinateRecordState {k : ℕ} (s : Fin k → ℝ)
    (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i ≤ 1) (j : Word k) : DensityState (Word k) :=
  pureState (coordinateRecordVector s j) (coordinateRecordVector_norm hs0 hs1 j)

/-- Exact guessing probability for the canonical Walsh ensemble with arbitrary binary overlaps. -/
theorem pGuess_coordinateRecord {k : ℕ} (s : Fin k → ℝ)
    (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i ≤ 1) :
    pGuess (uniformPrior (Word k)) (coordinateRecordState s hs0 hs1) =
      ∏ i, (1 + Real.sqrt (1 - (s i) ^ 2)) / 2 := by
  have h := pGuess_phase (walsh (k := k)) (coordinateWeight s) walsh_norm walsh_orthogonal
    (coordinateWeight_nonneg s) (coordinateWeight_sq_sum hs0 hs1)
  change pGuess (uniformPrior (Word k)) (coordinateRecordState s hs0 hs1) = _ at h
  rw [h]
  simp only [coordinateWeight, sum_words, sum_bool, ← Finset.prod_pow,
    bitWeight_add_sq (hs0 _) (hs1 _), Finset.prod_div_distrib]
  rw [div_eq_inv_mul]
  simp

/-- The canonical whole-record amplitude for equal coordinate overlaps. -/
def recordVector {k : ℕ} (s : ℝ) (j : Word k) : Word k → ℂ :=
  coordinateRecordVector (fun _ => s) j

theorem recordVector_norm {k : ℕ} {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (j : Word k) :
    star (recordVector s j) ⬝ᵥ recordVector s j = 1 :=
  coordinateRecordVector_norm (fun _ => hs0) (fun _ => hs1) j

/-- The normalized canonical states for equal coordinate overlaps. -/
def recordState {k : ℕ} (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (j : Word k) :
    DensityState (Word k) :=
  coordinateRecordState (fun _ => s) (fun _ => hs0) (fun _ => hs1) j

/-- The exact optimum over joint POVMs, including both overlap endpoints and the empty word. -/
theorem pGuess_jointRecord (k : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    pGuess (uniformPrior (Word k)) (recordState s hs0 hs1) =
      ((1 + Real.sqrt (1 - s ^ 2)) / 2) ^ k := by
  change pGuess (uniformPrior (Word k))
    (coordinateRecordState (fun _ => s) (fun _ => hs0) (fun _ => hs1)) = _
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    pGuess_coordinateRecord (k := k) (fun _ => s) (fun _ => hs0) (fun _ => hs1)

end

end JointRecordDecoding
