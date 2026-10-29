/- GID: D5/S3/Quantum/Matrix/AnalyticPickKernel
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/AnalyticPickKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.MeanValue]
   utility: none
   digest: Analytic matrix Pick kernels and normalized boundary Hankel positivity. -/

/-
admission_basis: escape-witness
Cauchy averaging and a matrix congruence derive full finite block positivity
from holomorphy and pointwise positive real part. Radial and boundary limits
transport this positivity to the normalized third-order Hankel matrix.
These are classical Caratheodory, Pick and Loewner arguments.
-/


import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Matrix.Order
import D5.S3.Analytic.Characterizations.ShiftedHerglotzCriterion
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Tactic

/-! Full block positivity from Cauchy averaging, followed by analytic boundary limits. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Complex Matrix Metric Set Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology

namespace D5.S3.Quantum.Matrix.AnalyticPickKernel

private def phi (R : ℝ) (w η : ℂ) : ℂ :=
  (1 - star w * η / (R : ℂ) ^ 2)⁻¹

private def weight (R : ℝ) (z w η : ℂ) : ℂ :=
  star (phi R z η) * phi R w η

private lemma circle_denom_ne_zero {R : ℝ} (hR : 0 < R)
    {w η : ℂ} (hw : ‖w‖ < R) (hη : η ∈ closedBall 0 R) :
    1 - star w * η / (R : ℂ) ^ 2 ≠ 0 := by
  have hηnorm : ‖η‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hη
  have hu : ‖star w * η / (R : ℂ) ^ 2‖ < 1 := by
    rw [norm_div, norm_mul, norm_star, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR]
    apply (div_lt_one (sq_pos_of_pos hR)).2
    calc
      ‖w‖ * ‖η‖ ≤ ‖w‖ * R := mul_le_mul_of_nonneg_left hηnorm (norm_nonneg _)
      _ < R ^ 2 := by nlinarith
  intro hzero
  have heq : star w * η / (R : ℂ) ^ 2 = 1 := (sub_eq_zero.mp hzero).symm
  rw [heq] at hu
  norm_num at hu

private lemma phi_diffCont {R : ℝ} (hR : 0 < R)
    {w : ℂ} (hw : ‖w‖ < R) :
    DiffContOnCl ℂ (phi R w) (ball 0 R) := by
  have hd : DiffContOnCl ℂ
      (fun η : ℂ => 1 - star w * η / (R : ℂ) ^ 2) (ball 0 R) :=
    (show Differentiable ℂ
      (fun η : ℂ => 1 - star w * η / (R : ℂ) ^ 2) from by fun_prop).diffContOnCl
  simpa only [phi, Pi.inv_apply] using! hd.inv (fun η hη =>
    circle_denom_ne_zero hR hw (closure_ball_subset_closedBall hη))

private lemma phi_star_boundary {R : ℝ} (hR : 0 < R)
    {z η : ℂ} (hz : ‖z‖ < R) (hη : η ∈ sphere 0 R) :
    star (phi R z η) = η / (η - z) := by
  have hηnorm : ‖η‖ = R := by simpa [mem_sphere, dist_eq_norm] using hη
  have hηz : η - z ≠ 0 := by
    intro hzero
    have heq : η = z := sub_eq_zero.mp hzero
    rw [heq] at hηnorm
    linarith
  have hRC : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hmul : η * star η = (R : ℂ) ^ 2 := by
    calc
      η * star η = (Complex.normSq η : ℂ) := by
        simpa only [Complex.star_def, mul_comm] using
          (Complex.normSq_eq_conj_mul_self (z := η)).symm
      _ = (R : ℂ) ^ 2 := by
        rw [Complex.normSq_eq_norm_sq, hηnorm]
        norm_cast
  have hrel : η * (1 - z * star η / (R : ℂ) ^ 2) = η - z := by
    calc
      η * (1 - z * star η / (R : ℂ) ^ 2) =
          η - z * (η * star η) / (R : ℂ) ^ 2 := by ring
      _ = η - z := by rw [hmul]; simp [hRC]
  have hd : 1 - z * star η / (R : ℂ) ^ 2 ≠ 0 := by
    intro hzero
    apply hηz
    rw [← hrel, hzero, mul_zero]
  have hs : star (phi R z η) =
      (1 - z * star η / (R : ℂ) ^ 2)⁻¹ := by
    simp [phi, mul_comm]
  rw [hs, eq_div_iff hηz, ← hrel]
  calc
    _ = η * ((1 - z * star η / (R : ℂ) ^ 2)⁻¹ *
        (1 - z * star η / (R : ℂ) ^ 2)) := by ring
    _ = η := by rw [inv_mul_cancel₀ hd, mul_one]

private lemma star_phi_swap (R : ℝ) (z w : ℂ) :
    star (phi R z w) = phi R w z := by
  simp [phi, mul_comm]

private lemma star_weight_swap (R : ℝ) (z w η : ℂ) :
    star (weight R w z η) = weight R z w η := by
  simp [weight, mul_comm]

private lemma weight_continuousOn {R : ℝ} (hR : 0 < R)
    {z w : ℂ} (hz : ‖z‖ < R) (hw : ‖w‖ < R) :
    ContinuousOn (weight R z w) (sphere 0 R) := by
  exact ((phi_diffCont hR hz).continuousOn_ball.mono sphere_subset_closedBall).star.mul
    ((phi_diffCont hR hw).continuousOn_ball.mono sphere_subset_closedBall)

section BanachStar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]
  [StarAddMonoid E] [StarModule ℂ E] [StarModule ℝ E] [ContinuousStar E]

private lemma weighted_circleIntegrable {R : ℝ} (hR : 0 < R)
    {z w : ℂ} (hz : ‖z‖ < R) (hw : ‖w‖ < R)
    {F : ℂ → E} (hF : ContinuousOn F (sphere 0 R)) :
    CircleIntegrable (fun η => weight R z w η • F η) 0 R := by
  exact ((weight_continuousOn hR hz hw).smul hF).circleIntegrable hR.le

/-- The missing analytic mechanism: one actual Cauchy application to
    eta |-> phi R w eta • G eta, whose pole lies outside the closed disk. -/
private theorem circleAverage_weight_smul {R : ℝ} (hR : 0 < R)
    {G : ℂ → E} (hG : DiffContOnCl ℂ G (ball 0 R))
    {z w : ℂ} (hz : ‖z‖ < R) (hw : ‖w‖ < R) :
    Real.circleAverage (fun η => weight R z w η • G η) 0 R =
      phi R w z • G z := by
  have hf : DiffContOnCl ℂ (fun η => phi R w η • G η) (ball 0 |R|) := by
    simpa only [abs_of_pos hR] using (phi_diffCont hR hw).smul hG
  have hc := hf.circleAverage_smul_div (w := z)
    (by simpa [mem_ball, dist_eq_norm, abs_of_pos hR] using hz)
  calc
    Real.circleAverage (fun η => weight R z w η • G η) 0 R =
        Real.circleAverage (fun η => (η / (η - z)) • (phi R w η • G η)) 0 R := by
      apply Real.circleAverage_congr_sphere
      intro η hη
      have hη' : η ∈ sphere 0 R := by simpa only [abs_of_pos hR] using hη
      simp only [weight, phi_star_boundary hR hz hη', smul_smul]
    _ = phi R w z • G z := by simpa only [sub_zero] using hc

/-- Exact finite-circle Caratheodory identity, obtained by Cauchy and adjoint.
    No measure representation or kernel positivity is assumed. -/
private theorem caratheodory_circle_identity {R : ℝ} (hR : 0 < R)
    {G : ℂ → E} (hG : DiffContOnCl ℂ G (ball 0 R))
    {z w : ℂ} (hz : ‖z‖ < R) (hw : ‖w‖ < R) :
    Real.circleAverage
        (fun η => weight R z w η • (G η + star (G η))) 0 R =
      phi R w z • (G z + star (G w)) := by
  have hCG := hG.continuousOn_ball.mono sphere_subset_closedBall
  have hI := weighted_circleIntegrable hR hz hw hCG
  have hIS := weighted_circleIntegrable hR hz hw hCG.star
  have hSwap := weighted_circleIntegrable hR hw hz hCG
  have hs := (starL' ℝ : E ≃L[ℝ] E).toContinuousLinearMap.circleAverage_comp_comm hSwap
  have hpoint :
      (fun η => (starL' ℝ : E ≃L[ℝ] E) (weight R w z η • G η)) =
        (fun η => weight R z w η • star (G η)) := by
    funext η
    simp only [starL'_apply, star_smul, star_weight_swap]
  have hStar : Real.circleAverage
      (fun η => weight R z w η • star (G η)) 0 R =
        phi R w z • star (G w) := by
    change Real.circleAverage
        (fun η => (starL' ℝ : E ≃L[ℝ] E) (weight R w z η • G η)) 0 R =
      star (Real.circleAverage (fun η => weight R w z η • G η) 0 R) at hs
    rw [hpoint, circleAverage_weight_smul hR hG hw hz] at hs
    simpa only [star_smul, star_phi_swap] using hs
  calc
    Real.circleAverage
        (fun η => weight R z w η • (G η + star (G η))) 0 R =
        Real.circleAverage (fun η => weight R z w η • G η) 0 R +
          Real.circleAverage (fun η => weight R z w η • star (G η)) 0 R := by
      simp only [smul_add]
      exact Real.circleAverage_fun_add hI hIS
    _ = phi R w z • G z + phi R w z • star (G w) := by
      rw [circleAverage_weight_smul hR hG hz hw, hStar]
    _ = phi R w z • (G z + star (G w)) := (smul_add _ _ _).symm

end BanachStar

section FiniteMatrices

variable {d ι : Type*} [Fintype d] [Fintype ι] [DecidableEq d]

private def boundaryFeature (R : ℝ) (points : ι → ℂ) (η : ℂ) :
    Matrix d (ι × d) ℂ :=
  fun a b => if a = b.2 then phi R (points b.1) η else 0

private def boundaryMatrix (R : ℝ) (points : ι → ℂ)
    (G : ℂ → Matrix d d ℂ) (η : ℂ) : Matrix (ι × d) (ι × d) ℂ :=
  fun a b => weight R (points a.1) (points b.1) η *
    (G η + (G η)ᴴ) a.2 b.2

def caratheodoryGram (R : ℝ) (points : ι → ℂ)
    (G : ℂ → Matrix d d ℂ) : Matrix (ι × d) (ι × d) ℂ :=
  fun a b => (1 - star (points b.1) * points a.1 / (R : ℂ) ^ 2)⁻¹ *
    (G (points a.1) + (G (points b.1))ᴴ) a.2 b.2

private lemma boundaryMatrix_factor (R : ℝ) (points : ι → ℂ)
    (G : ℂ → Matrix d d ℂ) (η : ℂ) :
    boundaryMatrix R points G η =
      (boundaryFeature R points η)ᴴ * (G η + (G η)ᴴ) *
        boundaryFeature R points η := by
  classical
  ext a b
  simp [boundaryMatrix, boundaryFeature, weight, Matrix.mul_apply,
    Matrix.conjTranspose_apply, apply_ite, star_zero, mul_ite, ite_mul] <;> ring

private lemma circleAverage_matrix_apply {p q : Type*} [Fintype p] [Fintype q]
    {R : ℝ} {F : ℂ → Matrix p q ℂ} (hF : CircleIntegrable F 0 R)
    (a : p) (b : q) :
    (Real.circleAverage F 0 R) a b =
      Real.circleAverage (fun η => F η a b) 0 R := by
  let L : Matrix p q ℂ →L[ℝ] ℂ :=
    { toFun := fun M => M a b
      map_add' := by intros; rfl
      map_smul' := by intros; rfl
      cont := (continuous_apply b).comp (continuous_apply a) }
  symm
  have he := L.circleAverage_comp_comm hF
  change Real.circleAverage (fun η => F η a b) 0 R =
    (Real.circleAverage F 0 R) a b at he
  exact he

private lemma circleAverage_posSemidef {p : Type*} [Fintype p]
    {R : ℝ} (hR : 0 < R) {F : ℂ → Matrix p p ℂ}
    (hF : ∀ η ∈ sphere 0 R, (F η).PosSemidef) :
    (Real.circleAverage F 0 R).PosSemidef := by
  have hi : (0 : Matrix p p ℂ) ≤
      ∫ θ in 0..2 * Real.pi, F (circleMap 0 R θ) := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    apply MeasureTheory.integral_nonneg
    intro θ
    apply (hF _ _).nonneg
    simpa only [abs_of_pos hR] using circleMap_mem_sphere' 0 R θ
  have hip := hi.posSemidef
  simpa only [Real.circleAverage_def] using
    hip.smul (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹)

/-- Actual finite-circle matrix-valued positive-kernel theorem.
    The only positivity premise concerns actual boundary values G eta + G eta*.
    Arbitrary finite samples and d-dimensional vector tests are included. -/
theorem finite_circle_caratheodory_posSemidef {R : ℝ} (hR : 0 < R)
    {G : ℂ → Matrix d d ℂ} (hG : DiffContOnCl ℂ G (ball 0 R))
    (hPos : ∀ η ∈ sphere 0 R, (G η + (G η)ᴴ).PosSemidef)
    (points : ι → ℂ) (hp : ∀ i, ‖points i‖ < R) :
    (caratheodoryGram R points G).PosSemidef := by
  classical
  let F := boundaryMatrix R points G
  have hCG : ContinuousOn G (sphere 0 R) :=
    hG.continuousOn_ball.mono sphere_subset_closedBall
  have hEntry (a b : d) : ContinuousOn (fun η => G η a b) (sphere 0 R) :=
    (continuousOn_pi.mp (continuousOn_pi.mp hCG a) b)
  have hF : ContinuousOn F (sphere 0 R) := by
    apply continuousOn_pi.mpr
    intro a
    apply continuousOn_pi.mpr
    intro b
    simpa only [F, boundaryMatrix, Matrix.add_apply, Matrix.conjTranspose_apply,
      Complex.star_def, Pi.mul_apply, Pi.add_apply] using!
      (weight_continuousOn hR (hp a.1) (hp b.1)).mul
        ((hEntry a.2 b.2).add (hEntry b.2 a.2).star)
  have hFI := hF.circleIntegrable hR.le
  have hAvg : Real.circleAverage F 0 R = caratheodoryGram R points G := by
    ext a b
    rw [circleAverage_matrix_apply hFI a b]
    have hSmallI : CircleIntegrable
        (fun η => weight R (points a.1) (points b.1) η • (G η + star (G η))) 0 R := by
      apply weighted_circleIntegrable hR (hp a.1) (hp b.1)
      exact hCG.add hCG.star
    have hIdentity := caratheodory_circle_identity hR hG (hp a.1) (hp b.1)
    have hEntryIdentity := congrArg (fun M : Matrix d d ℂ => M a.2 b.2) hIdentity
    rw [circleAverage_matrix_apply hSmallI a.2 b.2] at hEntryIdentity
    simpa only [F, boundaryMatrix, caratheodoryGram, phi, Matrix.smul_apply,
      smul_eq_mul, Matrix.star_eq_conjTranspose] using hEntryIdentity
  have hAvgPos : (Real.circleAverage F 0 R).PosSemidef := by
    apply circleAverage_posSemidef hR
    intro η hη
    change (boundaryMatrix R points G η).PosSemidef
    rw [boundaryMatrix_factor]
    exact (hPos η hη).conjTranspose_mul_mul_same (boundaryFeature R points η)
  rwa [hAvg] at hAvgPos

/-- Radial closure needs no value or regularity on the unit circle. -/
theorem open_disk_caratheodory_posSemidef
    {G : ℂ → Matrix d d ℂ} (hG : DifferentiableOn ℂ G (ball 0 1))
    (hPos : ∀ η ∈ ball 0 1, (G η + (G η)ᴴ).PosSemidef)
    (points : ι → ℂ) (hp : ∀ i, ‖points i‖ < 1) :
    (caratheodoryGram 1 points G).PosSemidef := by
  have hR0 : ∀ᶠ R : ℝ in 𝓝[<] 1, 0 < R :=
    (lt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hR1 : ∀ᶠ R : ℝ in 𝓝[<] 1, R < 1 := self_mem_nhdsWithin
  have hPoints : ∀ᶠ R : ℝ in 𝓝[<] 1, ∀ i, ‖points i‖ < R := by
    rw [eventually_all]
    intro i
    exact (lt_mem_nhds (hp i)).filter_mono nhdsWithin_le_nhds
  have hEventually : ∀ᶠ R : ℝ in 𝓝[<] 1,
      (caratheodoryGram R points G).PosSemidef := by
    filter_upwards [hR0, hR1, hPoints] with R hR0 hR1 hpR
    have hClosed : closedBall (0 : ℂ) R ⊆ ball 0 1 := by
      intro η hη
      have hn : ‖η‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hη
      simpa [mem_ball, dist_eq_norm] using hn.trans_lt hR1
    exact finite_circle_caratheodory_posSemidef hR0
      (hG.diffContOnCl_ball hClosed)
      (fun η hη => hPos η (hClosed (sphere_subset_closedBall hη))) points hpR
  have hCont : ContinuousAt (fun R : ℝ => caratheodoryGram R points G) 1 := by
    apply continuousAt_pi.mpr
    intro a
    apply continuousAt_pi.mpr
    intro b
    have hden : 1 - star (points b.1) * points a.1 / ((1 : ℝ) : ℂ) ^ 2 ≠ 0 :=
      circle_denom_ne_zero (by norm_num : (0 : ℝ) < 1) (hp b.1)
        (by simpa [mem_closedBall, dist_eq_norm] using (hp a.1).le)
    have hPow : ContinuousAt (fun R : ℝ => (R : ℂ) ^ 2) 1 := by fun_prop
    have hQuot : ContinuousAt
        (fun R : ℝ => star (points b.1) * points a.1 / (R : ℂ) ^ 2) 1 :=
      continuousAt_const.div hPow (by norm_num)
    exact ((continuousAt_const.sub hQuot).inv₀ hden).mul continuousAt_const
  exact Matrix.posSemidef_is_closed.mem_of_tendsto
    (hCont.tendsto.mono_left nhdsWithin_le_nhds) hEventually

end FiniteMatrices

section CayleyDomain

open D5.S3.Analytic.Characterizations.ShiftedHerglotzCriterion

private def diskToUpper (u : ℂ) : ℂ := I * ((1 + u) / (1 - u))

private def upperToDisk (z : ℂ) : ℂ := (z - I) / (z + I)

private lemma disk_denom_ne_zero {u : ℂ} (hu : ‖u‖ < 1) : 1 - u ≠ 0 := by
  intro hzero
  have heq : u = 1 := (sub_eq_zero.mp hzero).symm
  simpa [heq] using hu

private lemma diskToUpper_im_pos {u : ℂ} (hu : ‖u‖ < 1) :
    0 < (diskToUpper u).im := by
  simpa [diskToUpper, shiftedCayleyTransform, sub_eq_add_neg] using
    (shifted_cayley_positive_imaginary_part 1 (-u) (by norm_num)).mpr
      (by simpa using hu)

private lemma diskToUpper_differentiableOn :
    DifferentiableOn ℂ diskToUpper (ball 0 1) := by
  intro u hu
  have hn : ‖u‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hu
  have hd : DifferentiableAt ℂ diskToUpper u := by
    unfold diskToUpper
    fun_prop (disch := exact disk_denom_ne_zero hn)
  exact hd.differentiableWithinAt

private lemma upper_denom_ne_zero {z : ℂ} (hz : 0 < z.im) : z + I ≠ 0 := by
  intro hzero
  have hi := congrArg Complex.im hzero
  simp only [add_im, I_im, zero_im] at hi
  linarith

private lemma upperToDisk_norm_lt {z : ℂ} (hz : 0 < z.im) :
    ‖upperToDisk z‖ < 1 := by
  unfold upperToDisk
  rw [norm_div]
  apply (div_lt_one (norm_pos_iff.mpr (upper_denom_ne_zero hz))).2
  apply (sq_lt_sq₀ (norm_nonneg (z - I)) (norm_nonneg (z + I))).mp
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, sub_re, sub_im, add_re, add_im, I_re, I_im]
  nlinarith

private lemma diskToUpper_upperToDisk {z : ℂ} (hz : 0 < z.im) :
    diskToUpper (upperToDisk z) = z := by
  have hd := upper_denom_ne_zero hz
  have hu := disk_denom_ne_zero (upperToDisk_norm_lt hz)
  change I * ((1 + (z - I) / (z + I)) / (1 - (z - I) / (z + I))) = z
  change 1 - (z - I) / (z + I) ≠ 0 at hu
  field_simp [hd, hu] <;> simp [Complex.I_sq] <;> ring

private lemma diskToUpper_cross (u v : ℂ) (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) :
    diskToUpper u - star (diskToUpper v) =
      2 * I * (1 - u * star v) / ((1 - u) * (1 - star v)) := by
  have hdu := disk_denom_ne_zero hu
  have hdv := disk_denom_ne_zero hv
  have hdvs : 1 - star v ≠ 0 := by simpa using star_ne_zero.mpr hdv
  simp only [diskToUpper, star_mul, star_div₀, star_sub, star_add, star_one,
    Complex.star_def, Complex.conj_I]
  have hdvs' : 1 - (starRingEnd ℂ) v ≠ 0 := hdvs
  field_simp [hdu, hdvs'] <;> ring

end CayleyDomain

section UpperHalfPlane

variable {d ι : Type*} [Fintype d] [Fintype ι] [DecidableEq d]

/-- The Hermitian imaginary part of a complex matrix. -/
def imaginaryPart (A : Matrix d d ℂ) : Matrix d d ℂ :=
  (-I / 2) • (A - Aᴴ)

/-- The full finite block Pick matrix, including distinct block-vector tests. -/
def pickGram (points : ι → ℂ) (T : ℂ → Matrix d d ℂ) :
    Matrix (ι × d) (ι × d) ℂ :=
  fun a b => (points a.1 - star (points b.1))⁻¹ *
    (T (points a.1) - (T (points b.1))ᴴ) a.2 b.2

/-- Holomorphy and nonnegative imaginary part imply positivity of every finite
matrix-valued Pick Gram matrix on the upper half-plane. -/
theorem upper_half_plane_pick_posSemidef
    {T : ℂ → Matrix d d ℂ}
    (hT : DifferentiableOn ℂ T {z | 0 < z.im})
    (hPos : ∀ z, 0 < z.im → (imaginaryPart (T z)).PosSemidef)
    (points : ι → ℂ) (hp : ∀ i, 0 < (points i).im) :
    (pickGram points T).PosSemidef := by
  classical
  let G : ℂ → Matrix d d ℂ := fun u => (-I) • T (diskToUpper u)
  have hMaps : MapsTo diskToUpper (ball 0 1) {z | 0 < z.im} := by
    intro u hu
    exact diskToUpper_im_pos (by simpa [mem_ball, dist_eq_norm] using hu)
  have hG : DifferentiableOn ℂ G (ball 0 1) :=
    (hT.comp diskToUpper_differentiableOn hMaps).const_smul (-I)
  have hGPos : ∀ u ∈ ball 0 1, (G u + (G u)ᴴ).PosSemidef := by
    intro u hu
    have heq : G u + (G u)ᴴ = (2 : ℝ) • imaginaryPart (T (diskToUpper u)) := by
      ext a b
      simp [G, imaginaryPart, Matrix.conjTranspose_smul, Complex.real_smul,
        Matrix.conjTranspose_apply, Complex.star_def]
      ring
    rw [heq]
    exact (hPos _ (hMaps hu)).smul (by norm_num : (0 : ℝ) ≤ 2)
  let u : ι → ℂ := fun i => upperToDisk (points i)
  have hu : ∀ i, ‖u i‖ < 1 := fun i => upperToDisk_norm_lt (hp i)
  have hL := open_disk_caratheodory_posSemidef hG hGPos u hu
  let C : Matrix (ι × d) (ι × d) ℂ := diagonal (fun a => 1 - u a.1)
  have hCong := (hL.mul_mul_conjTranspose_same C).smul
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hEq : pickGram points T = (1 / 2 : ℝ) •
      (C * caratheodoryGram 1 u G * Cᴴ) := by
    ext a b
    have hda := disk_denom_ne_zero (hu a.1)
    have hdb := disk_denom_ne_zero (hu b.1)
    have hdbs : 1 - star (u b.1) ≠ 0 := by simpa using star_ne_zero.mpr hdb
    have hc : 1 - star (u b.1) * u a.1 ≠ 0 := by
      simpa using circle_denom_ne_zero (by norm_num : (0 : ℝ) < 1) (hu b.1)
        (by simpa [mem_closedBall, dist_eq_norm] using (hu a.1).le)
    have hc' : 1 - u a.1 * star (u b.1) ≠ 0 := by simpa [mul_comm] using hc
    have ha : diskToUpper (u a.1) = points a.1 := diskToUpper_upperToDisk (hp a.1)
    have hb : diskToUpper (u b.1) = points b.1 := diskToUpper_upperToDisk (hp b.1)
    have hcross := diskToUpper_cross (u a.1) (u b.1) (hu a.1) (hu b.1)
    rw [ha, hb] at hcross
    simp only [pickGram, Matrix.smul_apply, C, Matrix.diagonal_conjTranspose,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [hcross]
    simp only [caratheodoryGram, G, Matrix.conjTranspose_smul,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.conjTranspose_apply, smul_eq_mul, ha, hb,
      ofReal_one, one_pow, div_one, Complex.real_smul]
    simp only [Pi.star_apply, star_sub, star_one, star_neg, Complex.star_def, Complex.conj_I,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at *
    field_simp [hda, hdbs, hc, hc']
    ring_nf
    simp [Complex.I_sq]
    <;> ring

  rw [hEq]
  exact hCong

end UpperHalfPlane

end D5.S3.Quantum.Matrix.AnalyticPickKernel
