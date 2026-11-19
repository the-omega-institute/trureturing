/- GID: D5/S3/Entropy/Hypergraphs/FiniteFourier
   generality: G
   mirror-B: D5/B/S3/Entropy/Hypergraphs/FiniteFourier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Fourier inversion, Gaussian point bounds and entropy estimates. -/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic


/-! These are consumed proof-organizing auxiliaries, not independent escape witnesses.
Their general finite identities and estimates have proof_shape: bind-only.
The circular-law theorem is their actual consumer; its concrete geometric and
joint-law construction supplies the delivery's admission_basis: escape-witness. -/

public section

namespace D5.S3.Entropy.Hypergraphs.FiniteFourier

open scoped BigOperators

open MeasureTheory

private lemma integer_fourier_integral (z : ℤ) :
    (∫ t in -Real.pi..Real.pi,
      Complex.exp ((z : ℂ) * Complex.I * (t : ℂ))) =
      if z = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hz : z = 0
  · subst z
    simp
    ring
  · rw [ite_eq_right hz, integral_exp_mul_complex (by
      exact mul_ne_zero (by exact_mod_cast hz) Complex.I_ne_zero)]
    have he : Complex.exp ((z : ℂ) * Complex.I * (Real.pi : ℂ)) =
        Complex.exp ((z : ℂ) * Complex.I * (-Real.pi : ℂ)) := by
      have h : Complex.exp ((z : ℂ) * Complex.I * (Real.pi : ℂ)) /
          Complex.exp ((z : ℂ) * Complex.I * (-Real.pi : ℂ)) = 1 := by
        rw [← Complex.exp_sub]
        convert Complex.exp_int_mul_two_pi_mul_I z using 1; congr 1; ring
      exact (div_eq_one_iff_eq (Complex.exp_ne_zero _)).mp h
    simp only [Complex.ofReal_neg]
    rw [he, sub_self, zero_div]

private lemma sine_square_lower {t : ℝ}
    (ht : t ∈ Set.Icc (-Real.pi) Real.pi) :
    t ^ 2 / Real.pi ^ 2 ≤ Real.sin (t / 2) ^ 2 := by
  have habs : |t| ≤ Real.pi := abs_le.mpr ht
  have hh : |t / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right habs (by norm_num)
  have h := Real.mul_abs_le_abs_sin hh
  have h' : |t| / Real.pi ≤ |Real.sin (t / 2)| := by
    convert h using 1
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ |t| / Real.pi)
    (abs_nonneg (Real.sin (t / 2)))).2 h'
  simpa only [div_pow, sq_abs] using hs

private lemma gaussian_domination {A t : ℝ} (hA : 0 ≤ A)
    (ht : t ∈ Set.Icc (-Real.pi) Real.pi) :
    Real.exp (-A * Real.sin (t / 2) ^ 2) ≤
      Real.exp (-(A / Real.pi ^ 2) * t ^ 2) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (sine_square_lower ht) hA
  convert neg_le_neg h using 1 <;> ring

-- Applies directly to a characteristic function or its unit-modulus centered phase.
-- It does not assume the point-probability conclusion.
private lemma characteristic_integral_bound (f : ℝ → ℂ) {A : ℝ}
    (hA : 0 < A)
    (hf : ∀ t : ℝ, ‖f t‖ ≤ Real.exp (-A * Real.sin (t / 2) ^ 2)) :
    ‖∫ t in -Real.pi..Real.pi, f t‖ ≤
      Real.sqrt (Real.pi / (A / Real.pi ^ 2)) := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hb : 0 < A / Real.pi ^ 2 := div_pos hA (sq_pos_of_pos Real.pi_pos)
  have hi := integrable_exp_neg_mul_sq hb
  calc
    ‖∫ t in -Real.pi..Real.pi, f t‖ ≤
        ∫ t in -Real.pi..Real.pi, Real.exp (-(A / Real.pi ^ 2) * t ^ 2) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hpi
      · exact Filter.Eventually.of_forall fun t ht =>
          (hf t).trans (gaussian_domination hA.le ⟨ht.1.le, ht.2⟩)
      · exact hi.intervalIntegrable
    _ ≤ ∫ t : ℝ, Real.exp (-(A / Real.pi ^ 2) * t ^ 2) := by
      rw [intervalIntegral.integral_of_le hpi]
      exact setIntegral_le_integral hi
        (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
    _ = Real.sqrt (Real.pi / (A / Real.pi ^ 2)) := integral_gaussian _

-- Finite Fourier inversion before division by the sample-space cardinality.
-- The RHS is 2*pi times the literal count of the requested fibre.
private lemma finite_fourier_inversion {Ω : Type*} [Fintype Ω]
    (X : Ω → ℤ) (k : ℤ) :
    (∫ t in -Real.pi..Real.pi,
      ∑ ω : Ω, Complex.exp (((X ω - k : ℤ) : ℂ) * Complex.I * (t : ℂ))) =
      (2 * Real.pi : ℂ) * (∑ ω : Ω, if X ω = k then (1 : ℂ) else 0) := by
  classical
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [integer_fourier_integral, sub_eq_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> simp
  · intro ω _
    exact (by fun_prop : Continuous (fun t : ℝ =>
      Complex.exp (((X ω - k : ℤ) : ℂ) * Complex.I * (t : ℂ)))).intervalIntegrable _ _


private lemma centered_phase_identity {Ω : Type*} [Fintype Ω]
    (X : Ω → ℤ) (k : ℤ) (t : ℝ) :
    (∑ ω : Ω, Complex.exp (((X ω - k : ℤ) : ℂ) * Complex.I * (t : ℂ))) /
        (Fintype.card Ω : ℂ) =
      Complex.exp ((- (k : ℂ)) * Complex.I * (t : ℂ)) *
        ((∑ ω : Ω, Complex.exp ((X ω : ℂ) * Complex.I * (t : ℂ))) /
          (Fintype.card Ω : ℂ)) := by
  rw [← mul_div_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma centered_phase_norm {Ω : Type*} [Fintype Ω]
    (X : Ω → ℤ) (k : ℤ) (t : ℝ) :
    ‖(∑ ω : Ω, Complex.exp (((X ω - k : ℤ) : ℂ) * Complex.I * (t : ℂ))) /
        (Fintype.card Ω : ℂ)‖ =
      ‖(∑ ω : Ω, Complex.exp ((X ω : ℂ) * Complex.I * (t : ℂ))) /
        (Fintype.card Ω : ℂ)‖ := by
  rw [centered_phase_identity, norm_mul]
  have hp : ‖Complex.exp ((- (k : ℂ)) * Complex.I * (t : ℂ))‖ = 1 := by
    have he : (- (k : ℂ)) * Complex.I * (t : ℂ) =
        (((-(k : ℝ)) * t : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [he]
    exact Complex.norm_exp_ofReal_mul_I ((-(k : ℝ)) * t)
  rw [hp, one_mul]

private lemma gaussian_constant_normalization {A : ℝ} (hA : 0 < A) :
    Real.sqrt (Real.pi / (A / Real.pi ^ 2)) =
      (2 * Real.pi) * (Real.sqrt Real.pi / (2 * Real.sqrt A)) := by
  have hq : Real.pi / (A / Real.pi ^ 2) = Real.pi ^ 2 * (Real.pi / A) := by
    field_simp [ne_of_gt hA, Real.pi_ne_zero]
  rw [hq, Real.sqrt_mul (sq_nonneg Real.pi),
    Real.sqrt_sq Real.pi_pos.le, Real.sqrt_div Real.pi_pos.le]
  ring

lemma finite_uniform_mass_bound {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℤ) (k : ℤ) {A : ℝ} (hA : 0 < A)
    (hφ : ∀ t : ℝ,
      ‖(∑ ω : Ω, Complex.exp ((X ω : ℂ) * Complex.I * (t : ℂ))) /
        (Fintype.card Ω : ℂ)‖ ≤ Real.exp (-A * Real.sin (t / 2) ^ 2)) :
    (((Finset.univ.filter (fun ω : Ω => X ω = k)).card : ℝ) / Fintype.card Ω) ≤
      Real.sqrt Real.pi / (2 * Real.sqrt A) := by
  classical
  let f : ℝ → ℂ := fun t =>
    (∑ ω : Ω, Complex.exp (((X ω - k : ℤ) : ℂ) * Complex.I * (t : ℂ))) /
      (Fintype.card Ω : ℂ)
  have hf (t : ℝ) : ‖f t‖ ≤ Real.exp (-A * Real.sin (t / 2) ^ 2) := by
    dsimp only [f]
    rw [centered_phase_norm]
    exact hφ t
  have hb := characteristic_integral_bound f hA hf
  have hi : (∫ t in -Real.pi..Real.pi, f t) =
      (((2 * Real.pi) *
        ((Finset.univ.filter (fun ω : Ω => X ω = k)).card : ℝ) /
        (Fintype.card Ω : ℝ) : ℝ) : ℂ) := by
    dsimp only [f]
    rw [intervalIntegral.integral_div, finite_fourier_inversion]
    simp only [Finset.sum_boole]
    push_cast
    ring
  rw [hi, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), gaussian_constant_normalization hA] at hb
  have hp : 0 < (2 : ℝ) * Real.pi := by positivity
  have hc : (2 * Real.pi) *
      (((Finset.univ.filter (fun ω : Ω => X ω = k)).card : ℝ) / Fintype.card Ω) ≤
      (2 * Real.pi) * (Real.sqrt Real.pi / (2 * Real.sqrt A)) := by
    convert hb using 1; ring
  nlinarith


private theorem finite_mass_sum {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℕ) (n : ℕ) (hX : ∀ ω, X ω ≤ n) :
    ∑ k ∈ Finset.range (n + 1),
      ((Finset.univ.filter (fun ω : Ω => X ω = k)).card : ℝ) / Fintype.card Ω = 1 := by
  classical
  have hc : ∑ k ∈ Finset.range (n + 1),
      (Finset.univ.filter (fun ω : Ω => X ω = k)).card = Fintype.card Ω := by
    simp only [Finset.card_eq_sum_ones]
    rw [Finset.sum_fiberwise_of_maps_to (fun ω (_ : ω ∈ (Finset.univ : Finset Ω)) =>
      show X ω ∈ Finset.range (n + 1) from Finset.mem_range.mpr (by have := hX ω; omega))]
    simp
  rw [← Finset.sum_div]
  have hcast : ∑ k ∈ Finset.range (n + 1),
      ((Finset.univ.filter (fun ω : Ω => X ω = k)).card : ℝ) = Fintype.card Ω := by
    exact_mod_cast hc
  rw [hcast, div_self]
  exact_mod_cast Fintype.card_ne_zero

theorem finite_entropy_lower {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℕ) (n : ℕ) (hX : ∀ ω, X ω ≤ n) (C : ℝ)
    (_hC : 0 < C)
    (hbound : ∀ k, ((Finset.univ.filter (fun ω : Ω => X ω = k)).card : ℝ) /
      Fintype.card Ω ≤ C) :
    -Real.logb 2 C ≤ ∑ k ∈ Finset.range (n + 1),
      let p := ((Finset.univ.filter (fun ω : Ω => X ω = k)).card : ℝ) / Fintype.card Ω;
      -p * Real.logb 2 p := by
  classical
  let p : ℕ → ℝ := fun k =>
    ((Finset.univ.filter (fun ω : Ω => X ω = k)).card : ℝ) / Fintype.card Ω
  have hp (k : ℕ) : 0 ≤ p k := by dsimp [p]; positivity
  have hsum : ∑ k ∈ Finset.range (n + 1), p k = 1 := finite_mass_sum X n hX
  calc
    _ = ∑ k ∈ Finset.range (n + 1), p k * (-Real.logb 2 C) := by
      rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      change p k * (-Real.logb 2 C) ≤ -p k * Real.logb 2 (p k)
      by_cases hz : p k = 0
      · simp [hz]
      · have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
          (lt_of_le_of_ne (hp k) (Ne.symm hz)) (hbound k)
        have h := mul_le_mul_of_nonneg_left hlog (hp k)
        nlinarith

theorem finite_mass_le_one {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℕ) (k : ℕ) :
    ((Finset.univ.filter (fun ω : Ω => X ω = k)).card : ℝ) / Fintype.card Ω ≤ 1 := by
  apply (div_le_one (by exact_mod_cast Fintype.card_pos (α := Ω))).2
  exact_mod_cast (Finset.card_le_card (Finset.filter_subset (fun ω : Ω => X ω = k) Finset.univ))


end D5.S3.Entropy.Hypergraphs.FiniteFourier
