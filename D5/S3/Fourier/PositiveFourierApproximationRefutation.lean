/- GID: D5/S3/Fourier/PositiveFourierApproximationRefutation
   generality: I
   mirror-B: D5/B/S3/Fourier/PositiveFourierApproximationRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Fourier/PositiveFourierApproximationRefutation.claim; result=D5/S3/Fourier/PositiveFourierApproximationRefutation.result; claim=D5/S3/Fourier/PositiveFourierApproximationRefutation.claim
   digest: Herrera conjecture refuted. -/

/-
proof_shape (definitions):
  IsAdmissible: definition; approxCost: definition; approxError: definition;
  OperatorMonotoneOn: definition; claim: definition.
proof_shape (same-delivery helpers):
  abs_sin_nat_mul_le: bind-only; consumer: one_sub_cos_nat_mul_le.
  one_sub_cos_nat_mul_le: bind-only; consumer: admissible_deriv_defect.
  defect_dilation_abstract: bind-only; consumer: admissible_defect_properties.
  admissible_cos_rep: bind-only; consumer: admissible_deriv_defect.
  cosine_integrable: bind-only; consumer: admissible_deriv_defect.
  admissible_deriv_defect: bind-only; consumer: admissible_defect_properties.
  admissible_defect_properties: bind-only; consumer: uniform_cost_lower.
  three_point_bound_of_defect: bind-only; consumer: uniform_cost_lower.
  div_one_add_nonneg: bind-only; consumer: approx_values_nonempty and result.
  cfc_div_one_add_eq: bind-only; consumer: div_one_add_opmono.
  div_one_add_opmono: bind-only; consumer: result.
  zero_admissible: bind-only; consumer: approx_values_nonempty.
  div_one_add_le_one: bind-only; consumer: approx_values_nonempty.
  approx_values_nonempty: bind-only; consumer: approx_error_lower.
  uniform_cost_lower: bind-only; consumer: approx_error_lower.
  approx_error_lower: bind-only; consumer: result.
  result: bind-only; consumer: designated settling refutation.
escape_witness: none; the sine estimate is obtained by instantiating Mathlib's Chebyshev derivative bound.
The designated result is admitted by open-problem-resolution.
admission_basis: open-problem-resolution (#15279; Refuted)
Direct frozen dependencies: none; all proof steps use pinned Mathlib, including `Polynomial.Chebyshev.abs_iterate_derivative_T_real_le`.
The rational witness x/(1+x) is written inline; the only repository definition of it is the private `qPlus` of `CumulantRenyiDataProcessingRefutation`, a qubit-state parameter with no lemmas, so it is not imported.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
approxError is a real infimum. The refutation instance has a nonempty finite
cost set; no extended-real equivalence is claimed for targets without a
finite-cost approximant.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
open scoped Matrix.Norms.L2Operator
open scoped MatrixOrder
open scoped ComplexOrder
open MeasureTheory
noncomputable section

namespace D5.S3.Fourier.PositiveFourierApproximationRefutation


def IsAdmissible (g : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 g ∧ ∃ μ : MeasureTheory.Measure ℝ, MeasureTheory.IsFiniteMeasure μ ∧ ∀ x : ℝ, ((deriv g x : ℝ) : ℂ) = ∫ t, Complex.exp (-(↑t * ↑x) * Complex.I) ∂μ

def approxCost (f g : ℝ → ℝ) (c : ℝ) : ℝ :=
  (⨆ x : Set.Ici (0 : ℝ), (f x - g x)) - (⨅ x : Set.Ici (0 : ℝ), (f x - g x)) + c * deriv g 0

def approxError (f : ℝ → ℝ) (c : ℝ) : ℝ :=
  sInf {J | ∃ g, IsAdmissible g ∧ BddAbove (Set.range fun x : Set.Ici (0:ℝ) => f x - g x) ∧ BddBelow (Set.range fun x : Set.Ici (0:ℝ) => f x - g x) ∧ J = approxCost f g c}

def OperatorMonotoneOn (f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ), A.PosSemidef → B.PosSemidef → A ≤ B → cfc f A ≤ cfc f B

def claim : Prop := ∀ f : ℝ → ℝ, (∀ x, 0 ≤ x → 0 ≤ f x) → OperatorMonotoneOn f → ∀ c : ℝ, 0 < c → approxError f c ≤ f c
open Real

open Polynomial Polynomial.Chebyshev in
private lemma abs_sin_nat_mul_le (n : ℕ) (u : ℝ) : |sin (n * u)| ≤ (n : ℝ) * |sin u| := by
  by_cases hn0 : n = 0
  · simp [hn0]
  have hn : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have h := abs_iterate_derivative_T_real_le (n : ℤ) 1 (Real.abs_cos_le_one u)
  simp only [Function.iterate_one] at h
  rw [derivative_T_eval_one, T_derivative_eq_U] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_natCast, Int.cast_natCast,
    abs_mul, abs_of_pos hn] at h
  have hu : |(U ℝ ((n : ℤ) - 1)).eval (cos u)| ≤ (n : ℝ) := by nlinarith [h]
  have hs : (U ℝ ((n : ℤ) - 1)).eval (cos u) * sin u = sin ((n : ℝ) * u) := by
    simpa using U_real_cos u ((n : ℤ) - 1)
  calc
    |sin ((n : ℝ) * u)| = |(U ℝ ((n : ℤ) - 1)).eval (cos u)| * |sin u| := by
      rw [← hs, abs_mul]
    _ ≤ (n : ℝ) * |sin u| := mul_le_mul_of_nonneg_right hu (abs_nonneg _)

private lemma one_sub_cos_nat_mul_le (n : ℕ) (u : ℝ) :
    1 - cos (n * u) ≤ (n:ℝ)^2 * (1 - cos u) := by
  have h := abs_sin_nat_mul_le n (u / 2)
  have hs : (|sin (n * (u / 2))|)^2 ≤ ((n:ℝ) * |sin (u / 2)|)^2 := by nlinarith [abs_nonneg (sin (n * (u / 2))), abs_nonneg (sin (u / 2))]
  have hid (x : ℝ) : 1 - cos x = 2 * (|sin (x / 2)|)^2 := by
    rw [sq_abs]
    have hc := Real.cos_two_mul (x / 2)
    rw [show (2:ℝ) * (x / 2) = x by ring] at hc
    nlinarith [Real.sin_sq (x / 2)]
  rw [hid (n * u), hid u]
  have hh := mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 2)
  rw [mul_div_assoc]
  nlinarith [hh]


private lemma defect_dilation_abstract
    (d q : ℝ → ℝ) (N c : ℝ) (hN : 0 < N) (hc : 0 ≤ c)
    (hd0 : d 0 = 0)
    (hderiv : ∀ x, HasDerivAt d (q x) x)
    (hq_int : ∀ a b : ℝ, IntervalIntegrable q volume a b)
    (hq_scale : ∀ x, 0 ≤ x → x ≤ c → q (N*x) ≤ N^2 * q x) :
    d (N*c) ≤ N^3 * d c := by
  have hNc : 0 ≤ N*c := mul_nonneg (le_of_lt hN) hc
  have hFTC1 : d (N*c) - d 0 = ∫ x in 0..N*c, q x := by
    symm
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hderiv x) (hq_int 0 (N*c))
  have hFTC2 : d c - d 0 = ∫ x in 0..c, q x := by
    symm
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hderiv x) (hq_int 0 c)
  have hsub : (∫ x in 0..N*c, q x) = N * (∫ x in 0..c, q (N*x)) := by
    have h := intervalIntegral.integral_comp_mul_left q (ne_of_gt hN) (a := 0) (b := c) (c := N)
    rw [h]
    simp [smul_eq_mul]
    field_simp
  have hmono : (∫ x in 0..c, q (N*x)) ≤ ∫ x in 0..c, N^2 * q x := by
    apply intervalIntegral.integral_mono_on hc
    · have hi := (hq_int 0 (N*c)).comp_mul_left (c := N)
      convert hi using 1 <;> field_simp <;> simp
    · exact (hq_int 0 c).const_mul (N^2)
    · intro x hx
      exact hq_scale x hx.1 hx.2
  have hdN : d (N*c) = ∫ x in 0..N*c, q x := by rw [← hFTC1, hd0, sub_zero]
  have hdc : d c = ∫ x in 0..c, q x := by rw [← hFTC2, hd0, sub_zero]
  rw [hdN, hdc, hsub]
  calc
    N * (∫ x in 0..c, q (N*x)) ≤ N * (∫ x in 0..c, N^2 * q x) := mul_le_mul_of_nonneg_left hmono (le_of_lt hN)
    _ = N^3 * (∫ x in 0..c, q x) := by rw [intervalIntegral.integral_const_mul]; ring

private lemma admissible_cos_rep {g : ℝ → ℝ} (hg : IsAdmissible g) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧
      ∀ x, deriv g x = ∫ t, Real.cos (t*x) ∂μ := by
  obtain ⟨hcd, μ, hμ, hfour⟩ := hg
  letI := hμ
  refine ⟨μ, hμ, ?_⟩
  intro x
  have hint : Integrable (fun t : ℝ => Complex.exp (-(↑t * ↑x) * Complex.I)) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all μ (fun t => by simp [Complex.norm_exp])
  have heq := congrArg Complex.re (hfour x)
  change deriv g x = RCLike.re (∫ t : ℝ, Complex.exp (-(↑t * ↑x) * Complex.I) ∂μ) at heq
  rw [← integral_re hint] at heq
  simpa [Complex.exp_re, Complex.mul_re, Complex.mul_im] using heq

private lemma cosine_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    Integrable (fun t : ℝ => Real.cos (t*x)) μ := by
  apply Integrable.of_bound (by fun_prop) 1
  exact ae_of_all μ (fun t => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t*x))

private lemma admissible_deriv_defect {g : ℝ → ℝ} (hg : IsAdmissible g) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧
      (deriv g 0 = μ.real Set.univ) ∧
      (∀ s, deriv g 0 - deriv g s = ∫ t, (1 - Real.cos (t*s)) ∂μ) ∧
      (∀ s, 0 ≤ deriv g 0 - deriv g s) ∧
      (∀ (N : ℕ) s, deriv g 0 - deriv g ((N:ℝ)*s) ≤
        (N:ℝ)^2 * (deriv g 0 - deriv g s)) := by
  obtain ⟨μ, hμ, hcos⟩ := admissible_cos_rep hg
  letI := hμ
  have hzero : deriv g 0 = ∫ _ : ℝ, (1:ℝ) ∂μ := by simpa using hcos 0
  have hdef (s : ℝ) : deriv g 0 - deriv g s = ∫ t, (1 - Real.cos (t*s)) ∂μ := by
    rw [hzero, hcos s, integral_sub (integrable_const 1) (cosine_integrable μ s)]
  refine ⟨μ, hμ, ?_, hdef, ?_, ?_⟩
  · simpa using hzero
  · intro s
    rw [hdef]
    exact integral_nonneg (fun t => sub_nonneg.mpr (Real.cos_le_one _))
  · intro N s
    rw [hdef, hdef, ← integral_const_mul]
    apply integral_mono
    · exact (integrable_const 1).sub (cosine_integrable μ ((N:ℝ)*s))
    · exact ((integrable_const 1).sub (cosine_integrable μ s)).const_mul _
    · intro t
      change 1 - Real.cos (t * ((N:ℝ)*s)) ≤ (N:ℝ)^2 * (1 - Real.cos (t*s))
      rw [show t * ((N:ℝ)*s) = (N:ℝ)*(t*s) by ring]
      exact one_sub_cos_nat_mul_le N (t*s)

private lemma admissible_defect_properties {g : ℝ → ℝ} (hg : IsAdmissible g) :
    (∀ x, 0 ≤ x → 0 ≤ x * deriv g 0 - (g x - g 0)) ∧
    (∀ (N : ℕ) c, 0 ≤ c →
      ((N:ℝ)*c) * deriv g 0 - (g ((N:ℝ)*c) - g 0) ≤
        (N:ℝ)^3 * (c * deriv g 0 - (g c - g 0))) := by
  obtain ⟨μ, hμ, hzero, hdef, hnon, hscale⟩ := admissible_deriv_defect hg
  let d := fun x => x * deriv g 0 - (g x - g 0)
  let q := fun x => deriv g 0 - deriv g x
  have hd0 : d 0 = 0 := by simp [d]
  have hqcont : Continuous q := continuous_const.sub (hg.1.continuous_deriv le_rfl)
  have hd : ∀ x, HasDerivAt d (q x) x := by
    intro x
    have h := ((hasDerivAt_id x).mul_const (deriv g 0)).sub
      (((hg.1.differentiable (by norm_num)) x).hasDerivAt.sub_const (g 0))
    convert h using 1 <;> first | rfl | simp [d, q, Pi.sub_apply]
  constructor
  · intro x hx
    have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => hd y)
      (hqcont.intervalIntegrable 0 x)
    have hn := intervalIntegral.integral_nonneg (μ := volume) hx (fun y hy => hnon y)
    change 0 ≤ ∫ y in 0..x, q y at hn
    rw [hf] at hn
    simpa only [hd0, sub_zero, d] using hn
  · intro N c hc
    cases N with
    | zero => simp
    | succ n =>
      simpa only [d, Nat.cast_add, Nat.cast_one] using
        defect_dilation_abstract d q ((n+1:ℕ):ℝ) c (by positivity) hc hd0 hd
          (fun a b => hqcont.intervalIntegrable a b)
          (fun x hx hxc => hscale (n+1) x)


private lemma three_point_bound_of_defect (f g : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (hc : 0 ≤ c) (hf0 : f 0 = 0)
    (hbA : BddAbove (Set.range fun x : Set.Ici (0:ℝ) => f x - g x))
    (hbB : BddBelow (Set.range fun x : Set.Ici (0:ℝ) => f x - g x))
    (hd : ∀ x, 0 ≤ x → 0 ≤ x * deriv g 0 - (g x - g 0))
    (hscale : ((N:ℝ)*c)*deriv g 0 - (g ((N:ℝ)*c) - g 0) ≤
      (N:ℝ)^3 * (c*deriv g 0 - (g c - g 0))) :
    ((N:ℝ)^3 + (N:ℝ) + 2) * (approxCost f g c - f c) ≥
      ((N:ℝ)+1)*f (2*c) - ((N:ℝ)+2)*f c - f ((N:ℝ)*c) := by
  let W := (⨆ x : Set.Ici (0:ℝ), f x - g x) - (⨅ x : Set.Ici (0:ℝ), f x - g x)
  have bounds (x : ℝ) (hx : 0 ≤ x) :
      -W ≤ f x - g x + g 0 ∧ f x - g x + g 0 ≤ W := by
    have ha := le_ciSup hbA (⟨x,hx⟩ : Set.Ici (0:ℝ))
    have hb := ciInf_le hbB (⟨x,hx⟩ : Set.Ici (0:ℝ))
    have ha0 := le_ciSup hbA (⟨0,by simp⟩ : Set.Ici (0:ℝ))
    have hb0 := ciInf_le hbB (⟨0,by simp⟩ : Set.Ici (0:ℝ))
    dsimp at ha hb ha0 hb0
    dsimp [W]
    rw [hf0] at ha0 hb0
    constructor <;> linarith
  let e := W + c*deriv g 0 - f c
  have hde : c*deriv g 0 - (g c - g 0) ≤ e := by
    have hb := (bounds c hc).2
    dsimp [e]
    linarith
  have hlo : f (2*c) - f c - e ≤ c*deriv g 0 := by
    have hb := (bounds (2*c) (by positivity)).2
    have hd2 := hd (2*c) (by positivity)
    dsimp [e]
    linarith
  have hNnon : 0 ≤ (N:ℝ)^3 := by positivity
  have hNsc : ((N:ℝ)*c)*deriv g 0 - (g ((N:ℝ)*c) - g 0) ≤ (N:ℝ)^3 * e :=
    hscale.trans (mul_le_mul_of_nonneg_left hde hNnon)
  have hhi : ((N:ℝ)+1) * (c*deriv g 0) ≤ f ((N:ℝ)*c) + f c + ((N:ℝ)^3+1)*e := by
    have hb := (bounds ((N:ℝ)*c) (by positivity)).1
    dsimp [e] at *
    nlinarith only [hb, hNsc]
  have hm := mul_le_mul_of_nonneg_left hlo (show 0 ≤ (N:ℝ)+1 by positivity)
  change ((N:ℝ)^3 + (N:ℝ) + 2) * e ≥ _
  nlinarith only [hm, hhi]


open Matrix


private lemma div_one_add_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ (fun x : ℝ => x / (1 + x)) x := by
  dsimp
  positivity

private lemma cfc_div_one_add_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) :
    cfc (fun x : ℝ => x / (1 + x)) A = 1 - Ring.inverse (1 + A) := by
  have hs : ∀ x ∈ spectrum ℝ A, (1 + x) ≠ 0 := by
    intro x hx hzero
    have hnon : 0 ≤ x := spectrum_nonneg_of_nonneg hA.nonneg hx
    linarith
  calc
    cfc (fun x : ℝ => x / (1 + x)) A = cfc (fun x : ℝ => 1 - (1 + x)⁻¹) A := by
      apply cfc_congr
      intro x hx
      dsimp
      field_simp [hs x hx]
      ring
    _ = cfc (fun _ : ℝ => 1) A - cfc (fun x : ℝ => (1 + x)⁻¹) A := by
      exact cfc_sub _ _ A (hf := continuousOn_const)
        (hg := (continuous_const.add continuous_id).continuousOn.inv₀ hs)
    _ = 1 - Ring.inverse (cfc (fun x : ℝ => 1 + x) A) := by
      rw [cfc_const (1:ℝ) A (ha := IsSelfAdjoint.of_nonneg hA.nonneg),
        cfc_inv (fun x : ℝ => 1 + x) A hs
          (hf := (continuous_const.add continuous_id).continuousOn)
          (ha := IsSelfAdjoint.of_nonneg hA.nonneg)]
      simp
    _ = 1 - Ring.inverse (1 + A) := by
      change 1 - Ring.inverse (cfc (fun x : ℝ => 1 + id x) A) = _
      rw [cfc_add A (fun _ : ℝ => 1) id,
        cfc_const (1:ℝ) A (ha := IsSelfAdjoint.of_nonneg hA.nonneg),
        cfc_id ℝ A (ha := IsSelfAdjoint.of_nonneg hA.nonneg)]
      simp

private lemma div_one_add_opmono :
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ), A.PosSemidef → B.PosSemidef → A ≤ B → cfc (fun x : ℝ => x / (1 + x)) A ≤ cfc (fun x : ℝ => x / (1 + x)) B := by
  intro n A B hA hB hAB
  rw [cfc_div_one_add_eq A hA, cfc_div_one_add_eq B hB]
  have ha : IsStrictlyPositive (1 + A) := by
    apply IsStrictlyPositive.add_nonneg (a := (1 : Matrix (Fin n) (Fin n) ℂ))
    · exact isStrictlyPositive_one
    · exact hA.nonneg
  have hab : (1 + A) ≤ (1 + B) := by simpa [add_comm] using add_le_add_left hAB 1
  have hi : Ring.inverse (1 + B) ≤ Ring.inverse (1 + A) :=
    CStarAlgebra.ringInverse_le_ringInverse hab (ha := ha)
  exact sub_le_sub_left hi 1


private lemma zero_admissible : IsAdmissible (fun _ : ℝ => 0) := by
  refine ⟨contDiff_const, 0, inferInstance, ?_⟩
  intro x
  simp

private lemma div_one_add_le_one {x : ℝ} (hx : 0 ≤ x) : (fun x : ℝ => x / (1 + x)) x ≤ 1 := by
  dsimp
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 1+x)).mpr
  linarith

private lemma approx_values_nonempty :
    {J : ℝ | ∃ g, IsAdmissible g ∧
      BddAbove (Set.range fun x : Set.Ici (0:ℝ) => (fun x : ℝ => x / (1 + x)) x - g x) ∧
      BddBelow (Set.range fun x : Set.Ici (0:ℝ) => (fun x : ℝ => x / (1 + x)) x - g x) ∧
      J = approxCost (fun x : ℝ => x / (1 + x)) g 1}.Nonempty := by
  refine ⟨approxCost (fun x : ℝ => x / (1 + x)) (fun _ => 0) 1, (fun _ => 0), zero_admissible, ?_, ?_, rfl⟩
  · refine ⟨1, ?_⟩
    rintro y ⟨x,rfl⟩
    simpa using div_one_add_le_one x.property
  · refine ⟨0, ?_⟩
    rintro y ⟨x,rfl⟩
    simpa using div_one_add_nonneg x.property

private lemma uniform_cost_lower (g : ℝ → ℝ) (hg : IsAdmissible g)
    (hbA : BddAbove (Set.range fun x : Set.Ici (0:ℝ) => (fun x : ℝ => x / (1 + x)) x - g x))
    (hbB : BddBelow (Set.range fun x : Set.Ici (0:ℝ) => (fun x : ℝ => x / (1 + x)) x - g x)) :
    (1153:ℝ)/2304 ≤ approxCost (fun x : ℝ => x / (1 + x)) g 1 := by
  obtain ⟨hd, hscale⟩ := admissible_defect_properties hg
  have ht := three_point_bound_of_defect (fun x : ℝ => x / (1 + x)) g 1 11 (by norm_num)
    (by norm_num) hbA hbB hd (hscale 11 1 (by norm_num))
  norm_num at ht
  linarith

private lemma approx_error_lower : (1153:ℝ)/2304 ≤ approxError (fun x : ℝ => x / (1 + x)) 1 := by
  apply le_csInf approx_values_nonempty
  intro J hJ
  obtain ⟨g,hg,hbA,hbB,rfl⟩ := hJ
  exact uniform_cost_lower g hg hbA hbB

theorem result : ¬ claim := by
  intro hclaim
  have hup := hclaim (fun x : ℝ => x / (1 + x)) (fun x hx => div_one_add_nonneg hx) div_one_add_opmono 1 (by norm_num)
  have hlo := approx_error_lower
  norm_num at hup
  linarith


end D5.S3.Fourier.PositiveFourierApproximationRefutation
