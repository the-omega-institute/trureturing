/- GID: D5/S3/Analytic/PetzLogisticMatrixStrip
   generality: G
   mirror-B: D5/B/S3/Analytic/PetzLogisticMatrixStrip
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite matrix strips preserve reflected boundary comparisons under modular phases. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Analytic.PetzLogisticMidline
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Finite spectral strips in the Frobenius norm. -/

namespace PetzLogisticMatrixStrip

open Matrix MeasureTheory Set WithLp
open scoped Matrix.Norms.Frobenius InnerProductSpace

open private reflect_line from D5.S3.Analytic.PetzLogisticMidline

noncomputable section

variable {n m ι : Type*} [Fintype n] [Fintype m] [Fintype ι]

private def coordinates (X : Matrix n m ℂ) : EuclideanSpace ℂ (n × m) :=
  toLp 2 (fun ij => X ij.1 ij.2)

private theorem norm_coordinates (X : Matrix n m ℂ) : ‖coordinates X‖ = ‖X‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    Matrix.frobenius_norm_def, Fintype.sum_prod_type, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)]
  simp only [coordinates, PiLp.toLp_apply, Real.rpow_two]

private theorem differentiable_coordinates :
    Differentiable ℂ (coordinates (n := n) (m := m)) := by
  let L : Matrix n m ℂ →ₗ[ℂ] EuclideanSpace ℂ (n × m) :=
    { toFun := coordinates
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let C : Matrix n m ℂ →L[ℂ] EuclideanSpace ℂ (n × m) :=
    L.mkContinuous 1 (fun X => by
      change ‖coordinates X‖ ≤ 1 * ‖X‖
      rw [one_mul, norm_coordinates])
  exact C.differentiable

private theorem coordinates_inner (X Y : Matrix n m ℂ) :
    ⟪coordinates Y, coordinates X⟫_ℂ = (Yᴴ * X).trace := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Matrix.trace, Finset.sum_comm]
  simp only [coordinates, PiLp.toLp_apply, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.inner_apply, Complex.star_def, mul_comm]

/-- A closed-strip residual controls the full logistic energy of any physical
boundary pair with the same cross term. Its two squared norms can include
additional contributions from the support projections. -/
theorem full_logistic_of_boundary_cross {F : ℂ → Matrix n m ℂ}
    (hc : ContinuousOn F PetzLogisticMidline.closedStrip)
    (hd : DifferentiableOn ℂ F PetzLogisticMidline.openStrip)
    {B : ℝ} (hb : ∀ z ∈ PetzLogisticMidline.closedStrip, ‖F z‖ ≤ B)
    (X Y : ℝ → Matrix n m ℂ)
    (hCross : ∀ t,
      ((F (PetzLogisticMidline.line (1 / 2) t))ᴴ * F (PetzLogisticMidline.line 0 t)).trace =
        ((Y t)ᴴ * X t).trace)
    (hLower : Integrable (fun t => PetzLogisticMidline.lowerWeight t * ‖X t‖ ^ 2))
    (hX : Integrable (fun t => PetzLogisticMidline.upperWeight t * ‖X t‖ ^ 2))
    (hY : Integrable (fun t => PetzLogisticMidline.upperWeight t * ‖Y t‖ ^ 2)) :
    let l := PetzLogisticMidline.lowerWeight
    let w := PetzLogisticMidline.upperWeight
    let v := PetzLogisticMidline.midlineWeight
    (∫ t, l t * ‖X t‖ ^ 2) + (∫ t, w t * ‖Y t‖ ^ 2) -
        (∫ t, w t * ‖Y t - X t‖ ^ 2) =
        (∫ t, (l t - w t) * ‖X t‖ ^ 2) +
          2 * (∫ t, v t * ‖F (PetzLogisticMidline.line (1 / 4) t)‖ ^ 2) := by
  dsimp only
  let w := PetzLogisticMidline.upperWeight
  let l := PetzLogisticMidline.lowerWeight
  let v := PetzLogisticMidline.midlineWeight
  let C : ℝ → ℝ := fun t => w t * ((Y t)ᴴ * X t).trace.re
  obtain ⟨hi, _, hm⟩ := PetzLogisticMidline.integral_midline
    (differentiable_coordinates.continuous.comp_continuousOn hc)
    (differentiable_coordinates.comp_differentiableOn hd)
    (fun z hz => (norm_coordinates (F z)).trans_le (hb z hz))
  have hCross' (t : ℝ) :
      w t * (PetzLogisticMidline.reflectedPair (coordinates ∘ F)
        (PetzLogisticMidline.line 0 t)).re = C t := by
    rw [PetzLogisticMidline.reflectedPair, reflect_line, sub_zero]
    exact congrArg (fun z : ℂ => w t * z.re) ((coordinates_inner _ _).trans (hCross t))
  change Integrable (fun t => w t * (PetzLogisticMidline.reflectedPair (coordinates ∘ F)
    (PetzLogisticMidline.line 0 t)).re) at hi
  change (∫ t, w t * (PetzLogisticMidline.reflectedPair (coordinates ∘ F)
    (PetzLogisticMidline.line 0 t)).re) = _ at hm
  rw [funext hCross'] at hi hm
  have hMid : (∫ t, C t) = ∫ t, v t * ‖F (PetzLogisticMidline.line (1 / 4) t)‖ ^ 2 := by
    simpa only [Function.comp_apply, norm_coordinates] using hm
  have hPoint (t : ℝ) :
      w t * ‖Y t - X t‖ ^ 2 =
        w t * ‖Y t‖ ^ 2 + w t * ‖X t‖ ^ 2 - 2 * C t := by
    rw [← norm_coordinates (Y t - X t),
      show coordinates (Y t - X t) = coordinates (Y t) - coordinates (X t) from rfl,
      norm_sub_sq (𝕜 := ℂ), coordinates_inner, norm_coordinates, norm_coordinates]
    simp only [show (RCLike.re : ℂ → ℝ) = Complex.re from rfl, C]
    ring
  change (∫ t, l t * ‖X t‖ ^ 2) + (∫ t, w t * ‖Y t‖ ^ 2) -
      (∫ t, w t * ‖Y t - X t‖ ^ 2) =
      (∫ t, (l t - w t) * ‖X t‖ ^ 2) +
        2 * (∫ t, v t * ‖F (PetzLogisticMidline.line (1 / 4) t)‖ ^ 2)
  rw [show (fun t => w t * ‖Y t - X t‖ ^ 2) =
    (fun t => w t * ‖Y t‖ ^ 2 + w t * ‖X t‖ ^ 2 - 2 * C t) from funext hPoint]
  simp_rw [sub_mul]
  change Integrable (fun t => w t * ‖Y t‖ ^ 2) at hY
  change Integrable (fun t => w t * ‖X t‖ ^ 2) at hX
  change Integrable (fun t => l t * ‖X t‖ ^ 2) at hLower
  have hSum : Integrable (fun t => w t * ‖Y t‖ ^ 2 + w t * ‖X t‖ ^ 2) := hY.add hX
  rw [integral_sub hSum (hi.const_mul 2), integral_add hY hX,
    integral_const_mul, hMid, integral_sub hLower hX]
  ring

/-- Finite matrix spectral sums with real frequencies are entire. -/
theorem differentiable_exp_sum (ω : ι → ℝ) (C : ι → Matrix n m ℂ) :
    Differentiable ℂ (fun z => ∑ i, Complex.exp ((ω i : ℂ) * z) • C i) := by
  fun_prop

/-- Each finite matrix spectral sum is bounded on every strip with bounded real part. -/
theorem norm_exp_sum_le (ω : ι → ℝ) (C : ι → Matrix n m ℂ) {z : ℂ} {a : ℝ}
    (hz : |z.re| ≤ a) :
    ‖∑ i, Complex.exp ((ω i : ℂ) * z) • C i‖ ≤
      ∑ i, Real.exp (|ω i| * a) * ‖C i‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Complex.norm_exp]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [Real.exp_le_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc
    _ ≤ |ω i * z.re| := le_abs_self _
    _ = |ω i| * |z.re| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hz (abs_nonneg _)

/-- A common left and right unitary preserves the Frobenius energy of a residual. -/
theorem sq_norm_mul_unitaries {n : Type*} [Fintype n] [DecidableEq n]
    (L R X : Matrix n n ℂ) (hL : Lᴴ * L = 1) (hR : R * Rᴴ = 1) :
    ‖L * X * R‖ ^ 2 = ‖X‖ ^ 2 := by
  have htrace (Y : Matrix n n ℂ) : ‖Y‖ ^ 2 = (Y * Yᴴ).trace.re := by
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)]
    simp only [Real.rpow_two, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Complex.re_sum, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq, Complex.star_def]
  rw [htrace, htrace, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  congr 1
  rw [Matrix.mul_assoc (L * X) R, ← Matrix.mul_assoc R Rᴴ, hR, Matrix.one_mul,
    ← Matrix.mul_assoc (L * X) Xᴴ, Matrix.trace_mul_comm _ Lᴴ,
    ← Matrix.mul_assoc Lᴴ (L * X), ← Matrix.mul_assoc Lᴴ L, hL, Matrix.one_mul]

section Boundary

variable [DecidableEq n]

local notation "half" => ((1 / 2 : ℝ) : ℂ)
local notation "it " t => ((t : ℂ) * Complex.I)

/-- The residual before the common imaginary-power modulation. The arguments
are the source powers, the reference powers, and the lifted output product. -/
def residual (R S O : ℂ → Matrix n n ℂ) (z : ℂ) :=
  R half - S z * O z * R (half - z)

def commonAmplitude (R S : ℂ → Matrix n n ℂ) (t : ℝ) :=
  S (-(it t)) * R (half + it t)

def lowerAmplitude (R O : ℂ → Matrix n n ℂ) (t : ℝ) :=
  O (it t) * R half

def upperAmplitude (S O : ℂ → Matrix n n ℂ) (t : ℝ) :=
  S half * O (half + it t)

/-- One pair of imaginary-power multipliers transforms both boundary residuals.
The third equality transfers their difference with the same multipliers. -/
theorem boundary_norms (R S O : ℂ → Matrix n n ℂ)
    (Radd : ∀ z w, R z * R w = R (z + w))
    (Sadd : ∀ z w, S z * S w = S (z + w))
    (Rzero : R 0 = 1) (Szero : S 0 = 1)
    (Radj : ∀ z, (R z)ᴴ = R (star z))
    (Sadj : ∀ z, (S z)ᴴ = S (star z))
    (t : ℝ) :
    let f := residual R S O
    let U := commonAmplitude R S t
    let L := lowerAmplitude R O t
    let H := upperAmplitude S O t
    ‖f (PetzLogisticMidline.line 0 t)‖ ^ 2 = ‖U - L‖ ^ 2 ∧
      ‖f (PetzLogisticMidline.line (1 / 2) t)‖ ^ 2 = ‖U - H‖ ^ 2 ∧
      ‖f (PetzLogisticMidline.line (1 / 2) t) - f (PetzLogisticMidline.line 0 t)‖ ^ 2 =
        ‖L - H‖ ^ 2 := by
  let p : ℂ := it t
  have hp : star p = -p := by simp [p, mul_neg]
  have hLeft : (S (-p))ᴴ * S (-p) = 1 := by
    rw [Sadj, star_neg, hp, neg_neg, Sadd, add_neg_cancel, Szero]
  have hRight : R p * (R p)ᴴ = 1 := by
    rw [Radj, hp, Radd, add_neg_cancel, Rzero]
  have hMod₀ : S (-p) * residual R S O (PetzLogisticMidline.line 0 t) * R p =
      commonAmplitude R S t - lowerAmplitude R O t := by
    have hz : PetzLogisticMidline.line 0 t = p := by simp [PetzLogisticMidline.line, p]
    rw [hz, residual, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc (S (-p)) (R half),
      Radd, ← Matrix.mul_assoc (S (-p)) (S p * O p), ← Matrix.mul_assoc (S (-p)) (S p),
      Sadd, neg_add_cancel, Szero, Matrix.one_mul, Matrix.mul_assoc (O p), Radd,
      sub_add_cancel]
    rfl
  have hMod₁ : S (-p) * residual R S O (PetzLogisticMidline.line (1 / 2) t) * R p =
      commonAmplitude R S t - upperAmplitude S O t := by
    have hz : PetzLogisticMidline.line (1 / 2) t = half + p := rfl
    have h₁ : half - (half + p) = -p := by ring
    have h₂ : -p + (half + p) = half := by ring
    rw [hz, residual, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc (S (-p)) (R half),
      Radd, ← Matrix.mul_assoc (S (-p)) (S (half + p) * O (half + p)),
      ← Matrix.mul_assoc (S (-p)) (S (half + p)), Sadd, h₂,
      Matrix.mul_assoc (S half * O (half + p)), h₁, Radd, neg_add_cancel, Rzero, Matrix.mul_one]
    rfl
  have hModD : S (-p) * (residual R S O (PetzLogisticMidline.line (1 / 2) t) -
      residual R S O (PetzLogisticMidline.line 0 t)) * R p =
      lowerAmplitude R O t - upperAmplitude S O t := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hMod₁, hMod₀]
    abel
  exact ⟨(sq_norm_mul_unitaries _ _ _ hLeft hRight).symm.trans (congrArg (fun X => ‖X‖ ^ 2) hMod₀),
    (sq_norm_mul_unitaries _ _ _ hLeft hRight).symm.trans (congrArg (fun X => ‖X‖ ^ 2) hMod₁),
    (sq_norm_mul_unitaries _ _ _ hLeft hRight).symm.trans (congrArg (fun X => ‖X‖ ^ 2) hModD)⟩

omit [DecidableEq n] in
/-- The cross term survives singular input support. The lower residual already
has source right support and the upper residual already has reference left support.
Thus projecting the opposite corners in the analytic residual preserves their pairing. -/
theorem supported_boundary_cross (R S O : ℂ → Matrix n n ℂ)
    (Radd : ∀ z w, R z * R w = R (z + w))
    (Sadd : ∀ z w, S z * S w = S (z + w))
    (Radj : ∀ z, (R z)ᴴ = R (star z))
    (Sadj : ∀ z, (S z)ᴴ = S (star z))
    (hs : S 0 * R half = R half) (t : ℝ) :
    let F := residual R S O
    let U := commonAmplitude R S t
    let X := U - lowerAmplitude R O t
    let Y := U - upperAmplitude S O t
    ((F (PetzLogisticMidline.line (1 / 2) t))ᴴ *
      F (PetzLogisticMidline.line 0 t)).trace = (Yᴴ * X).trace := by
  let p : ℂ := it t
  let F := residual R S O
  let X := commonAmplitude R S t - lowerAmplitude R O t
  let Y := commonAmplitude R S t - upperAmplitude S O t
  let L := S (-p)
  let J := R p
  let A := F (PetzLogisticMidline.line 0 t)
  let B := F (PetzLogisticMidline.line (1 / 2) t)
  change (Bᴴ * A).trace = (Yᴴ * X).trace
  have hp : star p = -p := by simp [p, mul_neg]
  have hL : Lᴴ * L = S 0 := by
    rw [show L = S (-p) from rfl, Sadj, star_neg, hp, neg_neg, Sadd, add_neg_cancel]
  have hJ : J * Jᴴ = R 0 := by
    rw [show J = R p from rfl, Radj, hp, Radd, add_neg_cancel]
  have hAleft : S 0 * A = A := by
    simp only [A, F, residual, Matrix.mul_sub, hs, ← Matrix.mul_assoc, Sadd, zero_add]
  have hAright : A * R 0 = A := by
    simp only [A, F, residual, Matrix.sub_mul, Matrix.mul_assoc, Radd, add_zero]
  have hXright : X * R 0 = X := by
    simp only [X, commonAmplitude, lowerAmplitude, Matrix.sub_mul, Matrix.mul_assoc, Radd, add_zero]
  have hYleft : S 0 * Y = Y := by
    simp only [Y, commonAmplitude, upperAmplitude, Matrix.mul_sub, ← Matrix.mul_assoc,
      Sadd, zero_add]
  have hYadj : Yᴴ * S 0 = Yᴴ := by
    simpa only [Matrix.conjTranspose_mul, Sadj, star_zero] using
      congrArg Matrix.conjTranspose hYleft
  have hMod₀ : L * A * J = S 0 * X := by
    have hz : PetzLogisticMidline.line 0 t = p := by simp [PetzLogisticMidline.line, p]
    change S (-p) * residual R S O (PetzLogisticMidline.line 0 t) * R p =
      S 0 * (S (-p) * R (half + p) - O p * R half)
    rw [hz, residual, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc (S (-p)) (R half),
      Radd, ← Matrix.mul_assoc (S (-p)) (S p * O p), ← Matrix.mul_assoc (S (-p)) (S p),
      Sadd, neg_add_cancel, Matrix.mul_assoc, Radd, sub_add_cancel,
      Matrix.mul_sub, ← Matrix.mul_assoc (S 0) (S (-p)), Sadd, zero_add, Matrix.mul_assoc]
  have hMod₁ : L * B * J = Y * R 0 := by
    have hz : PetzLogisticMidline.line (1 / 2) t = half + p := rfl
    have h₁ : half - (half + p) = -p := by ring
    have h₂ : -p + (half + p) = half := by ring
    change S (-p) * residual R S O (PetzLogisticMidline.line (1 / 2) t) * R p =
      (S (-p) * R (half + p) - S half * O (half + p)) * R 0
    rw [hz, residual, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc (S (-p)) (R half),
      Radd, ← Matrix.mul_assoc (S (-p)) (S (half + p) * O (half + p)),
      ← Matrix.mul_assoc (S (-p)) (S (half + p)), Sadd, h₂,
      Matrix.mul_assoc (S half * O (half + p)), h₁, Radd, neg_add_cancel,
      Matrix.sub_mul, Matrix.mul_assoc (S (-p)), Radd, add_zero]
  calc
    _ = ((L * B * J)ᴴ * (L * A * J)).trace := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm Jᴴ]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Lᴴ L, hL, ← Matrix.mul_assoc (S 0) A, hAleft,
        hJ, hAright]
    _ = _ := by
      rw [hMod₀, hMod₁, Matrix.conjTranspose_mul, Radj, star_zero, Matrix.mul_assoc,
        Matrix.trace_mul_comm (R 0), ← Matrix.mul_assoc Yᴴ (S 0), hYadj,
        Matrix.mul_assoc Yᴴ X, hXright]

end Boundary

end

end PetzLogisticMatrixStrip
