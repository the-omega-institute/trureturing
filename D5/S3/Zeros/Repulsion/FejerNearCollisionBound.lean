/- GID: D5/S3/Zeros/Repulsion/FejerNearCollisionBound
   generality: G
   mirror-B: D5/B/S3/Zeros/Repulsion/FejerNearCollisionBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite Fejer energy bounds control near collisions and repeated values. -/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

noncomputable section

open scoped BigOperators ComplexConjugate
open Finset

namespace D5.S3.Zeros.Repulsion.FejerNearCollisionBound

/-- The unit complex phase at a real argument. -/
def phase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

@[simp] private theorem phase_re (x : ℝ) : (phase x).re = Real.cos x := by
  simp [phase]

@[simp] private theorem phase_im (x : ℝ) : (phase x).im = Real.sin x := by
  simp [phase]

@[simp] private theorem normSq_phase (x : ℝ) : Complex.normSq (phase x) = 1 := by
  rw [Complex.normSq_eq_norm_sq]
  simp [phase]

@[simp] private theorem phase_mul_conj_phase (x y : ℝ) :
    phase x * conj (phase y) = phase (x - y) := by
  rw [phase, phase, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp
  ring

/-- The length-`M` geometric exponential sum. -/
def exponentialSum (M : ℕ) (t : ℝ) : ℂ :=
  ∑ r ∈ range M, phase ((r : ℝ) * t)

private theorem pair_cosine_sum_eq_normSq {ι : Type*} [Fintype ι]
    (x : ι → ℝ) :
    (∑ i, ∑ j, Real.cos (x i - x j)) =
      Complex.normSq (∑ i, phase (x i)) := by
  simp only [Real.cos_sub, Finset.sum_add_distrib, Complex.normSq_apply,
    Complex.re_sum, Complex.im_sum, phase_re, phase_im]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]

/-- The Fejer kernel, with positive and negative modes paired. -/
def fejerKernel (M : ℕ) (t : ℝ) : ℝ :=
  1 + 2 * ∑ k ∈ range (M - 1),
    (1 - ((k + 1 : ℕ) : ℝ) / (M : ℝ)) *
      Real.cos (((k + 1 : ℕ) : ℝ) * t)

private def spectralEnergy {ι : Type*} [Fintype ι]
    (M : ℕ) (γ : ι → ℝ) : ℝ :=
  (Fintype.card ι : ℝ) ^ 2 +
    2 * ∑ k ∈ range (M - 1),
      (1 - ((k + 1 : ℕ) : ℝ) / (M : ℝ)) *
        Complex.normSq (∑ i, phase (((k + 1 : ℕ) : ℝ) * γ i))

/-- The signed-mode Fejer energy, split into zero, positive, and negative modes. -/
def signedSpectralEnergy {ι : Type*} [Fintype ι]
    (M : ℕ) (γ : ι → ℝ) : ℝ :=
  (Fintype.card ι : ℝ) ^ 2 +
    (∑ k ∈ range (M - 1),
      (1 - ((k + 1 : ℕ) : ℝ) / (M : ℝ)) *
        Complex.normSq (∑ i, phase (((k + 1 : ℕ) : ℝ) * γ i))) +
    ∑ k ∈ range (M - 1),
      (1 - ((k + 1 : ℕ) : ℝ) / (M : ℝ)) *
        Complex.normSq (∑ i, phase (-(((k + 1 : ℕ) : ℝ) * γ i)))

private theorem fejer_energy_identity_split {ι : Type*} [Fintype ι]
    (M : ℕ) (γ : ι → ℝ) :
    (∑ i, ∑ j, fejerKernel M (γ i - γ j)) = spectralEnergy M γ := by
  have hmode (k : ℕ) :
      (∑ i, ∑ j, Real.cos ((k : ℝ) * (γ i - γ j))) =
        Complex.normSq (∑ i, phase ((k : ℝ) * γ i)) := by
    simpa only [mul_sub] using
      (pair_cosine_sum_eq_normSq (x := fun i => (k : ℝ) * γ i))
  have hswap (f : ι → ι → ℕ → ℝ) (s : Finset ℕ) :
      (∑ i, ∑ j, ∑ k ∈ s, f i j k) =
        ∑ k ∈ s, ∑ i, ∑ j, f i j k := by
    calc
      (∑ i, ∑ j, ∑ k ∈ s, f i j k) =
          ∑ i, ∑ k ∈ s, ∑ j, f i j k := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_comm]
      _ = ∑ k ∈ s, ∑ i, ∑ j, f i j k := by
        rw [Finset.sum_comm]
  have hweighted :
      (∑ i, ∑ j, ∑ k ∈ range (M - 1),
        2 * ((1 - ((k + 1 : ℕ) : ℝ) / (M : ℝ)) *
          Real.cos (((k + 1 : ℕ) : ℝ) * (γ i - γ j)))) =
      ∑ k ∈ range (M - 1),
        2 * ((1 - ((k + 1 : ℕ) : ℝ) / (M : ℝ)) *
          Complex.normSq (∑ i, phase (((k + 1 : ℕ) : ℝ) * γ i))) := by
    rw [hswap]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      (∑ i, ∑ j,
          2 * ((1 - ((k + 1 : ℕ) : ℝ) / (M : ℝ)) *
            Real.cos (((k + 1 : ℕ) : ℝ) * (γ i - γ j)))) =
          (2 * (1 - ((k + 1 : ℕ) : ℝ) / (M : ℝ))) *
            (∑ i, ∑ j,
              Real.cos (((k + 1 : ℕ) : ℝ) * (γ i - γ j))) := by
                simp_rw [Finset.mul_sum]
                ring
      _ = _ := by rw [hmode]; ring
  simp only [fejerKernel, spectralEnergy, Finset.sum_add_distrib]
  simp_rw [Finset.mul_sum]
  rw [hweighted]
  simp
  ring

private theorem negative_mode_normSq_eq {ι : Type*} [Fintype ι]
    (n : ℕ) (γ : ι → ℝ) :
    Complex.normSq (∑ i, phase (-((n : ℝ) * γ i))) =
      Complex.normSq (∑ i, phase ((n : ℝ) * γ i)) := by
  simp only [Complex.normSq_apply, Complex.re_sum, Complex.im_sum,
    phase_re, phase_im, Real.cos_neg, Real.sin_neg,
    Finset.sum_neg_distrib]
  ring

private theorem signedSpectralEnergy_eq_spectralEnergy
    {ι : Type*} [Fintype ι] (M : ℕ) (γ : ι → ℝ) :
    signedSpectralEnergy M γ = spectralEnergy M γ := by
  simp only [signedSpectralEnergy, spectralEnergy]
  simp_rw [negative_mode_normSq_eq]
  ring

private theorem signed_mode_sum_eq_split {n M : ℕ} (hM : 1 ≤ M)
    (γ : Fin n → ℝ) :
    (∑ k ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter
        (fun k => |k| < (M : ℤ)),
      (1 - ((|k| : ℤ) : ℝ) / (M : ℝ)) *
        Complex.normSq (∑ i, phase ((k : ℝ) * γ i))) =
      signedSpectralEnergy M γ := by
  classical
  let modes := (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter
    (fun k => |k| < (M : ℤ))
  let pos := (Finset.range (M - 1)).image
    (fun k : ℕ => ((k + 1 : ℕ) : ℤ))
  let neg := (Finset.range (M - 1)).image
    (fun k : ℕ => -((k + 1 : ℕ) : ℤ))
  let term : ℤ → ℝ := fun k =>
    (1 - ((|k| : ℤ) : ℝ) / (M : ℝ)) *
      Complex.normSq (∑ i, phase ((k : ℝ) * γ i))
  have habsPos (k : ℕ) :
      |((k + 1 : ℕ) : ℤ)| = ((k + 1 : ℕ) : ℤ) :=
    abs_of_nonneg (by omega)
  have habsNeg (k : ℕ) :
      |(-((k + 1 : ℕ) : ℤ))| = ((k + 1 : ℕ) : ℤ) := by
    rw [abs_neg, habsPos]
  have hmodes : modes = {0} ∪ pos ∪ neg := by
    ext k
    simp only [modes, Finset.mem_filter, Finset.mem_Icc, abs_lt]
    cases k with
    | ofNat a =>
        cases a with
        | zero =>
            simp [pos, neg]
            omega
        | succ a =>
            simp [pos, neg]
            omega
    | negSucc a =>
        have hk : Int.negSucc a = -((a + 1 : ℕ) : ℤ) := by omega
        simp [pos, neg, hk]
        omega
  have hzeroPos : Disjoint ({0} : Finset ℤ) pos := by
    rw [Finset.disjoint_left]
    intro z hz hzp
    rw [Finset.mem_singleton] at hz
    rcases Finset.mem_image.mp hzp with ⟨k, hk, hzk⟩
    subst z
    omega
  have hnonnegNeg : Disjoint (({0} : Finset ℤ) ∪ pos) neg := by
    rw [Finset.disjoint_left]
    intro z hz hzn
    rcases Finset.mem_image.mp hzn with ⟨k, hk, hzk⟩
    rcases Finset.mem_union.mp hz with hz | hz
    · rw [Finset.mem_singleton] at hz
      omega
    · rcases Finset.mem_image.mp hz with ⟨j, hj, hzj⟩
      omega
  have hpos :
      (∑ k ∈ pos, term k) =
        ∑ k ∈ range (M - 1), term ((k + 1 : ℕ) : ℤ) := by
    simp only [pos]
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact Nat.add_right_cancel (Int.ofNat_inj.mp hab)
  have hneg :
      (∑ k ∈ neg, term k) =
        ∑ k ∈ range (M - 1), term (-((k + 1 : ℕ) : ℤ)) := by
    simp only [neg]
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact Nat.add_right_cancel (Int.ofNat_inj.mp (neg_inj.mp hab))
  have hzero : term 0 = (n : ℝ) ^ 2 := by
    simp [term, phase, pow_two]
  have htermPos (k : ℕ) :
      term ((k + 1 : ℕ) : ℤ) =
        (1 - ((k + 1 : ℕ) : ℝ) / (M : ℝ)) *
          Complex.normSq (∑ i, phase (((k + 1 : ℕ) : ℝ) * γ i)) := by
    dsimp only [term]
    rw [habsPos]
    push_cast
    rfl
  have htermNeg (k : ℕ) :
      term (-((k + 1 : ℕ) : ℤ)) =
        (1 - ((k + 1 : ℕ) : ℝ) / (M : ℝ)) *
          Complex.normSq (∑ i, phase (-(((k + 1 : ℕ) : ℝ) * γ i))) := by
    dsimp only [term]
    rw [habsNeg]
    push_cast
    simp only [neg_mul]
  change ∑ k ∈ modes, term k = signedSpectralEnergy M γ
  rw [hmodes, Finset.sum_union hnonnegNeg, Finset.sum_union hzeroPos,
    Finset.sum_singleton, hpos, hneg, hzero]
  simp_rw [htermPos, htermNeg]
  simp [signedSpectralEnergy]

/-- The finite Fejer pair energy is the sum over all signed modes `|k| < M`. -/
theorem fejer_energy_identity {n M : ℕ} (hM : 1 ≤ M) (γ : Fin n → ℝ) :
    (∑ i, ∑ j, fejerKernel M (γ i - γ j)) =
      ∑ k ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter
          (fun k => |k| < (M : ℤ)),
        (1 - ((|k| : ℤ) : ℝ) / (M : ℝ)) *
          Complex.normSq (∑ i, phase ((k : ℝ) * γ i)) := by
  rw [fejer_energy_identity_split, ← signedSpectralEnergy_eq_spectralEnergy]
  exact (signed_mode_sum_eq_split hM γ).symm

private theorem cross_term (n : ℕ) (t : ℝ) :
    (exponentialSum n t * conj (phase ((n : ℝ) * t))).re =
      ∑ k ∈ range n, Real.cos (((k + 1 : ℕ) : ℝ) * t) := by
  rw [exponentialSum, Finset.sum_mul, Complex.re_sum]
  simp only [phase_mul_conj_phase, phase_re]
  rw [← Finset.sum_range_reflect
    (fun k => Real.cos (((k + 1 : ℕ) : ℝ) * t)) n]
  apply Finset.sum_congr rfl
  intro r hr
  have hrlt : r < n := Finset.mem_range.mp hr
  rw [← Real.cos_neg]
  congr 1
  have hidx : n - 1 - r + 1 = n - r := by omega
  rw [hidx, Nat.cast_sub (Nat.le_of_lt hrlt)]
  ring

private theorem normSq_exponentialSum (M : ℕ) (t : ℝ) :
    Complex.normSq (exponentialSum M t) =
      (M : ℝ) + 2 * ∑ k ∈ range (M - 1),
        ((M : ℝ) - ((k + 1 : ℕ) : ℝ)) *
          Real.cos (((k + 1 : ℕ) : ℝ) * t) := by
  induction M with
  | zero => simp [exponentialSum]
  | succ n ih =>
      rw [show exponentialSum (n + 1) t =
          exponentialSum n t + phase ((n : ℝ) * t) by
        simp [exponentialSum, Finset.sum_range_succ]]
      rw [Complex.normSq_add, normSq_phase, cross_term, ih]
      cases n with
      | zero => simp
      | succ m =>
          simp only [Nat.add_sub_cancel]
          simp only [Nat.cast_add, Nat.cast_one]
          have hupdate :
              (∑ k ∈ range (m + 1),
                  ((m : ℝ) + 1 + 1 - ((k : ℝ) + 1)) *
                    Real.cos (((k : ℝ) + 1) * t)) =
                (∑ k ∈ range m,
                  ((m : ℝ) + 1 - ((k : ℝ) + 1)) *
                    Real.cos (((k : ℝ) + 1) * t)) +
                ∑ k ∈ range (m + 1),
                  Real.cos (((k : ℝ) + 1) * t) := by
            rw [Finset.sum_range_succ, Finset.sum_range_succ]
            rw [← add_assoc]
            congr 1
            · rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro k hk
              ring
            · ring
          linear_combination -2 * hupdate

/-- The Fejer cosine polynomial is the normalized square of a geometric sum. -/
theorem fejer_square {M : ℕ} (hM : 1 ≤ M) (t : ℝ) :
    fejerKernel M t =
      (1 / (M : ℝ)) * Complex.normSq (exponentialSum M t) := by
  rw [normSq_exponentialSum]
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  simp only [fejerKernel]
  field_simp [hM0]
  rw [mul_add, mul_one]
  congr 1
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  field_simp

@[simp] private theorem phase_nat_mul (n : ℕ) (t : ℝ) :
    phase ((n : ℝ) * t) = phase t ^ n := by
  rw [phase, phase, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem exponentialSum_mul (M : ℕ) (t : ℝ) :
    exponentialSum M t * (phase t - 1) = phase ((M : ℝ) * t) - 1 := by
  simpa only [exponentialSum, phase_nat_mul] using
    (geom_sum_mul (phase t) M)

private theorem norm_phase_sub_one (x : ℝ) :
    ‖phase x - 1‖ = |2 * Real.sin (x / 2)| := by
  simpa only [phase, mul_comm, Real.norm_eq_abs] using
    (Complex.norm_exp_I_mul_ofReal_sub_one x)

private theorem norm_exponentialSum_mul_sine (M : ℕ) (t : ℝ) :
    ‖exponentialSum M t‖ * |2 * Real.sin (t / 2)| =
      |2 * Real.sin (((M : ℝ) * t) / 2)| := by
  have h := congrArg norm (exponentialSum_mul M t)
  simpa only [norm_mul, norm_phase_sub_one] using h

/-- On `|t| <= pi/M`, the Fejer kernel is at least `4M/pi^2`. -/
theorem fejer_local_lower_bound {M : ℕ} (hM : 1 ≤ M) {t : ℝ}
    (ht : |t| ≤ Real.pi / (M : ℝ)) :
    4 * (M : ℝ) / Real.pi ^ 2 ≤ fejerKernel M t := by
  have hMpos : 0 < (M : ℝ) := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos hpi
  by_cases ht0 : t = 0
  · subst t
    rw [fejer_square hM]
    have hsum : exponentialSum M 0 = (M : ℂ) := by
      simp [exponentialSum, phase]
    rw [hsum, Complex.normSq_natCast]
    have hfour : (4 : ℝ) ≤ Real.pi ^ 2 := by
      nlinarith [Real.two_le_pi, sq_nonneg (Real.pi - 2)]
    calc
      4 * (M : ℝ) / Real.pi ^ 2 ≤ (M : ℝ) := by
        rw [div_le_iff₀ hpi2]
        nlinarith
      _ = (1 / (M : ℝ)) * ((M : ℝ) * (M : ℝ)) := by
        field_simp
  · have htpos : 0 < |t| := abs_pos.mpr ht0
    have hangle : |((M : ℝ) * t / 2)| ≤ Real.pi / 2 := by
      rw [abs_div, abs_mul, abs_of_pos hMpos,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
      calc
        (M : ℝ) * |t| ≤ (M : ℝ) * (Real.pi / (M : ℝ)) :=
          mul_le_mul_of_nonneg_left ht hMpos.le
        _ = Real.pi := by field_simp
    have hnumerator :
        2 * (M : ℝ) * |t| / Real.pi ≤
          |2 * Real.sin (((M : ℝ) * t) / 2)| := by
      have hsine := Real.mul_abs_le_abs_sin hangle
      have htwice := mul_le_mul_of_nonneg_left hsine (by norm_num : (0 : ℝ) ≤ 2)
      calc
        2 * (M : ℝ) * |t| / Real.pi =
            2 * (2 / Real.pi * |((M : ℝ) * t / 2)|) := by
              rw [abs_div, abs_mul, abs_of_pos hMpos,
                abs_of_pos (by norm_num : (0 : ℝ) < 2)]
              field_simp
        _ ≤ 2 * |Real.sin (((M : ℝ) * t) / 2)| := htwice
        _ = |2 * Real.sin (((M : ℝ) * t) / 2)| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hdenominator : |2 * Real.sin (t / 2)| ≤ |t| := by
      calc
        |2 * Real.sin (t / 2)| = 2 * |Real.sin (t / 2)| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        _ ≤ 2 * |t / 2| :=
          mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
        _ = |t| := by
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          ring
    have hnormMul :
        (2 * (M : ℝ) / Real.pi) * |t| ≤
          ‖exponentialSum M t‖ * |t| := by
      calc
        (2 * (M : ℝ) / Real.pi) * |t| =
            2 * (M : ℝ) * |t| / Real.pi := by ring
        _ ≤ |2 * Real.sin (((M : ℝ) * t) / 2)| := hnumerator
        _ = ‖exponentialSum M t‖ * |2 * Real.sin (t / 2)| :=
          (norm_exponentialSum_mul_sine M t).symm
        _ ≤ ‖exponentialSum M t‖ * |t| :=
          mul_le_mul_of_nonneg_left hdenominator (norm_nonneg _)
    have hnorm :
        2 * (M : ℝ) / Real.pi ≤ ‖exponentialSum M t‖ := by
      exact le_of_mul_le_mul_right hnormMul htpos
    have hsquare :
        (2 * (M : ℝ) / Real.pi) ^ 2 ≤ ‖exponentialSum M t‖ ^ 2 := by
      exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 hnorm
    rw [fejer_square hM, Complex.normSq_eq_norm_sq]
    calc
      4 * (M : ℝ) / Real.pi ^ 2 =
          (1 / (M : ℝ)) * (2 * (M : ℝ) / Real.pi) ^ 2 := by
            field_simp
            ring
      _ ≤ (1 / (M : ℝ)) * ‖exponentialSum M t‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare (by positivity)

private theorem fejer_nonnegative {M : ℕ} (hM : 1 ≤ M) (t : ℝ) :
    0 ≤ fejerKernel M t := by
  rw [fejer_square hM]
  exact mul_nonneg (by positivity) (Complex.normSq_nonneg _)

private theorem fejer_zero {M : ℕ} (hM : 1 ≤ M) :
    fejerKernel M 0 = (M : ℝ) := by
  rw [fejer_square hM]
  have hsum : exponentialSum M 0 = (M : ℂ) := by
    simp [exponentialSum, phase]
  rw [hsum, Complex.normSq_natCast]
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  field_simp

/-- Ordered index pairs whose values differ by at most `pi/M`. -/
def nearPairs {ι : Type*} [Fintype ι]
    (M : ℕ) (γ : ι → ℝ) : Finset (ι × ι) :=
  (Finset.univ.product Finset.univ).filter
    (fun p => |γ p.1 - γ p.2| ≤ Real.pi / (M : ℝ))

/-- The generic ordered near-pair count bound used by the atom-facing theorem. -/
private theorem near_pair_count_bound_aux {ι : Type*} [Fintype ι]
    {M : ℕ} (hM : 1 ≤ M) (γ : ι → ℝ) :
    ((nearPairs M γ).card : ℝ) ≤
      Real.pi ^ 2 / (4 * (M : ℝ)) *
        (∑ i, ∑ j, fejerKernel M (γ i - γ j)) := by
  classical
  let allPairs : Finset (ι × ι) := Finset.univ.product Finset.univ
  let c : ℝ := 4 * (M : ℝ) / Real.pi ^ 2
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hlocal :
      c * ((nearPairs M γ).card : ℝ) ≤
        ∑ p ∈ nearPairs M γ, fejerKernel M (γ p.1 - γ p.2) := by
    calc
      c * ((nearPairs M γ).card : ℝ) =
          ∑ p ∈ nearPairs M γ, c := by simp [mul_comm]
      _ ≤ ∑ p ∈ nearPairs M γ, fejerKernel M (γ p.1 - γ p.2) := by
        apply Finset.sum_le_sum
        intro p hp
        exact fejer_local_lower_bound hM (Finset.mem_filter.mp hp).2
  have hsubset : nearPairs M γ ⊆ allPairs := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have htoAll :
      (∑ p ∈ nearPairs M γ, fejerKernel M (γ p.1 - γ p.2)) ≤
        ∑ p ∈ allPairs, fejerKernel M (γ p.1 - γ p.2) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro p hp hpn
    exact fejer_nonnegative hM _
  have hscaled :
      c * ((nearPairs M γ).card : ℝ) ≤
        ∑ i, ∑ j, fejerKernel M (γ i - γ j) := by
    calc
      c * ((nearPairs M γ).card : ℝ) ≤
          ∑ p ∈ allPairs, fejerKernel M (γ p.1 - γ p.2) :=
        hlocal.trans htoAll
      _ = ∑ i, ∑ j, fejerKernel M (γ i - γ j) := by
        dsimp [allPairs]
        rw [Fintype.sum_prod_type]
  calc
    ((nearPairs M γ).card : ℝ) ≤
        (∑ i, ∑ j, fejerKernel M (γ i - γ j)) / c := by
      apply (le_div_iff₀ hcpos).2
      simpa [mul_comm] using hscaled
    _ = Real.pi ^ 2 / (4 * (M : ℝ)) *
        (∑ i, ∑ j, fejerKernel M (γ i - γ j)) := by
      dsimp [c]
      field_simp

/-- The ordered near-pair count is bounded by the total Fejer energy. -/
theorem near_pair_count_bound {n : ℕ} {M : ℕ} (hM : 1 ≤ M)
    (γ : Fin n → ℝ) :
    ((((Finset.univ.product Finset.univ).filter
      (fun p : Fin n × Fin n =>
        |γ p.1 - γ p.2| ≤ Real.pi / (M : ℝ))).card : ℕ) : ℝ) ≤
      Real.pi ^ 2 / (4 * (M : ℝ)) *
        (∑ i, ∑ j, fejerKernel M (γ i - γ j)) := by
  change ((nearPairs M γ).card : ℝ) ≤
    Real.pi ^ 2 / (4 * (M : ℝ)) *
      (∑ i, ∑ j, fejerKernel M (γ i - γ j))
  exact near_pair_count_bound_aux hM γ

private def multiplicitySquareMass {ι : Type*} [Fintype ι]
    (γ : ι → ℝ) : ℝ :=
  ∑ i, ((Finset.univ.filter (fun j => γ j = γ i)).card : ℝ)

/-- The sum of squared multiplicities over the distinct values attained by `γ`. -/
def distinctMultiplicitySquareMass {ι : Type*} [Fintype ι]
    (γ : ι → ℝ) : ℝ :=
  ∑ v ∈ Finset.univ.image γ,
    ((Finset.univ.filter (fun i => γ i = v)).card : ℝ) ^ 2

private theorem multiplicitySquareMass_eq_distinct
    {ι : Type*} [Fintype ι] (γ : ι → ℝ) :
    multiplicitySquareMass γ = distinctMultiplicitySquareMass γ := by
  classical
  rw [multiplicitySquareMass, distinctMultiplicitySquareMass]
  symm
  calc
    (∑ v ∈ Finset.univ.image γ,
        ((Finset.univ.filter (fun i => γ i = v)).card : ℝ) ^ 2) =
        ∑ v ∈ Finset.univ.image γ,
          ∑ i ∈ Finset.univ.filter (fun i => γ i = v),
            ((Finset.univ.filter (fun j => γ j = v)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro v hv
      simp [pow_two]
    _ = ∑ v ∈ Finset.univ.image γ,
          ∑ i ∈ Finset.univ.filter (fun i => γ i = v),
            ((Finset.univ.filter (fun j => γ j = γ i)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = ∑ i,
          ((Finset.univ.filter (fun j => γ j = γ i)).card : ℝ) := by
      exact Finset.sum_fiberwise_of_maps_to
        (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩) _

private theorem multiplicity_energy_lower_bound
    {ι : Type*} [Fintype ι] {M : ℕ} (hM : 1 ≤ M) (γ : ι → ℝ) :
    (M : ℝ) * multiplicitySquareMass γ ≤
      ∑ i, ∑ j, fejerKernel M (γ i - γ j) := by
  classical
  simp only [multiplicitySquareMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  let fiber : Finset ι := Finset.univ.filter (fun j => γ j = γ i)
  calc
    (M : ℝ) * (fiber.card : ℝ) =
        ∑ j ∈ fiber, fejerKernel M (γ i - γ j) := by
      calc
        (M : ℝ) * (fiber.card : ℝ) =
            ∑ j ∈ fiber, (M : ℝ) := by simp [mul_comm]
        _ = ∑ j ∈ fiber, fejerKernel M (γ i - γ j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [show γ i - γ j = 0 by
            have hj' := (Finset.mem_filter.mp hj).2
            linarith, fejer_zero hM]
    _ ≤ ∑ j, fejerKernel M (γ i - γ j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro j hj hjf
        exact fejer_nonnegative hM _

/-- Fejer energy dominates `M` times the squared multiplicities of distinct values. -/
theorem distinct_multiplicity_energy_lower_bound
    {n : ℕ} {M : ℕ} (hM : 1 ≤ M) (γ : Fin n → ℝ) :
    (M : ℝ) *
        (∑ v ∈ Finset.univ.image γ,
          ((Finset.univ.filter (fun i => γ i = v)).card : ℝ) ^ 2) ≤
      ∑ i, ∑ j, fejerKernel M (γ i - γ j) := by
  change (M : ℝ) * distinctMultiplicitySquareMass γ ≤
    ∑ i, ∑ j, fejerKernel M (γ i - γ j)
  rw [← multiplicitySquareMass_eq_distinct]
  exact multiplicity_energy_lower_bound hM γ

/-- Concrete domain and hypothesis witness for the near-pair theorem. -/
example :
    (((nearPairs 1 (fun i : Fin 2 => ((i : ℕ) : ℝ))).card : ℝ)) ≤
      Real.pi ^ 2 / 4 *
        (∑ i : Fin 2, ∑ j : Fin 2,
          fejerKernel 1 (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ))) := by
  simpa [nearPairs] using
    (near_pair_count_bound (M := 1) (by norm_num)
      (fun i : Fin 2 => ((i : ℕ) : ℝ)))

#print axioms fejer_square
#print axioms fejer_energy_identity
#print axioms fejer_local_lower_bound
#print axioms near_pair_count_bound
#print axioms distinct_multiplicity_energy_lower_bound

end D5.S3.Zeros.Repulsion.FejerNearCollisionBound
