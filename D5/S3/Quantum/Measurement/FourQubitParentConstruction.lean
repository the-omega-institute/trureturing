/- GID: D5/S3/Quantum/Measurement/FourQubitParentConstruction
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/FourQubitParentConstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bloch coordinates and an exact joint parent for four noisy qubit POVMs. -/
/-
  B_formula: proof_shape: bind-only; escape_witness: none; consumer: scalarB_det.
  B_smul: proof_shape: bind-only; escape_witness: none; consumer: B_real_smul.
  B_real_smul: proof_shape: bind-only; escape_witness: none; consumer: weighted_noisy_unbiased.
  B_neg: proof_shape: bind-only; escape_witness: none;
    consumer: FourQubitCompatibilityDegree.noisy_optimal_difference.
  B_sum: proof_shape: bind-only; escape_witness: none; consumer: scalarB_sum.
  norm_sq_coords: proof_shape: bind-only; escape_witness: none; consumer: scalarB_det.
  trace_B_mul: proof_shape: bind-only; escape_witness: none;
    consumer: FourQubitCompatibilityDegree.dual_value.
  scalarB_posSemidef_iff: proof_shape: bind-only; escape_witness: none;
    consumer: half_scalarB_posSemidef_iff, unbiased_parent.
  half_scalarB_posSemidef_iff: proof_shape: bind-only; escape_witness: none;
    consumer: povm_bloch_coordinates, noisy_povm.
  povm_bloch_coordinates: proof_shape: bind-only; escape_witness: none;
    consumer: all_povms_compatible.
  endpoint_mem_Icc: proof_shape: bind-only; escape_witness: none;
    consumer: all_povms_compatible.
  compatible_of_parent: proof_shape: bind-only; escape_witness: none;
    consumer: unbiased_compatible, FourQubitCompatibilityDegree.optimal_endpoint_compatible.
  all_povms_compatible: proof_shape: content; escape_witness: all_povms_compatible.
  admission_basis: escape-witness (all_povms_compatible).
  Direct frozen dependencies:
    D5/S3/Combinatorics/IsingUniquenessSets.sgn
      statement_id: sha256:1589788918111821cb994915047b9b43151423396895fcfd849105cc8fe4d481
    D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM
      statement_id: sha256:218e2b42c4dc29468db56af33ad277eb32b8ed575533012439ed233131c5efa1
    D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix
      statement_id: sha256:7f853eaeda888a9eccbab5fe25474fc62b519a3229013530986887de25cb28d7
    D5/S3/Quantum/Information/ActualPureQubitGeometry.bloch
      statement_id: sha256:cc88c714292e1a1b7f96163a344340fa2144c8b2caffc5cb2196fb9df44fd3e5
    D5/S3/Quantum/FiniteDimensional.qubitX
      statement_id: sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7
    D5/S3/Quantum/FiniteDimensional.qubitZ
      statement_id: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
  Same-delivery prerequisite: FourVectorSignSumBound.four_vector_inequality.
  Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14767.
  Utility is none: the universal analytic parent construction is the main content;
  finite identities are consumed in its proof and in the extremal certificates.
-/
import D5.S3.Geometry.FourVectorSignSumBound
import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.Quantum.Information.ActualPureQubitGeometry
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
noncomputable section
open Matrix
open D5.S3.Combinatorics.IsingUniquenessSets (sgn)
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (pauliMatrix)
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum (bloch)
open D5.S3.Geometry.FourVectorSignSumBound
namespace D5.S3.Quantum.Measurement.FourQubitParentConstruction
def Compatible4 (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) : Prop :=
  (∀ i, IsPOVM (E i)) ∧ ∃ J : ((Fin 4 → Bool) → Matrix (Fin 2) (Fin 2) ℂ), IsPOVM J ∧
    ∀ i b, E i b = ∑ ε with ε i = b, J ε
def noisy (s : ℝ) (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ) :=
  fun i b => s • E i b + (1 - s) • ((1 / 2 : ℂ) • (1 : (Matrix (Fin 2) (Fin 2) ℂ)))
def endpoint : ℝ := 2 / Real.sqrt 13
def B (a : (EuclideanSpace ℝ (Fin 3))) : (Matrix (Fin 2) (Fin 2) ℂ) :=
  (a 0 : ℂ) • pauliMatrix .X + (a 1 : ℂ) • pauliMatrix .Y +
    (a 2 : ℂ) • pauliMatrix .Z
theorem B_formula (a : (EuclideanSpace ℝ (Fin 3))) :
    B a = !![(a 2 : ℂ), (a 0 : ℂ) - Complex.I * (a 1 : ℂ);
      (a 0 : ℂ) + Complex.I * (a 1 : ℂ), -(a 2 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B, pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
@[simp] private theorem B_zero : B (0 : (EuclideanSpace ℝ (Fin 3))) = 0 := by
  simp [B]
@[simp] private theorem B_add (a b : (EuclideanSpace ℝ (Fin 3))) : B (a + b) = B a + B b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B_formula] <;> ring
@[simp] private theorem B_smul (c : ℝ) (a : (EuclideanSpace ℝ (Fin 3))) : B (c • a) = (c : ℂ) • B a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B_formula] <;> ring
theorem B_real_smul (c : ℝ) (a : (EuclideanSpace ℝ (Fin 3))) : B (c • a) = c • B a := by
  calc
    B (c • a) = (c : ℂ) • B a := B_smul c a
    _ = c • B a := (RCLike.real_smul_eq_coe_smul (K := ℂ) c (B a)).symm
@[simp] theorem B_neg (a : (EuclideanSpace ℝ (Fin 3))) : B (-a) = -B a := by
  simpa using B_smul (-1) a
theorem B_sum {ι : Type*} (s : Finset ι) (a : ι → (EuclideanSpace ℝ (Fin 3))) :
    B (∑ i ∈ s, a i) = ∑ i ∈ s, B (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi h => simp [hi, h]
theorem norm_sq_coords (a : (EuclideanSpace ℝ (Fin 3))) : ‖a‖ ^ 2 = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 := by
  simpa [Fin.sum_univ_three] using EuclideanSpace.real_norm_sq_eq a
theorem trace_B_mul (a b : (EuclideanSpace ℝ (Fin 3))) : Matrix.trace (B a * B b) =
    (2 * inner ℝ a b : ℝ) := by
  apply Complex.ext <;>
    simp [B_formula, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
      PiLp.inner_apply, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im] <;> ring
def scalarB (t : ℝ) (a : (EuclideanSpace ℝ (Fin 3))) : (Matrix (Fin 2) (Fin 2) ℂ) := (t : ℂ) • (1 : (Matrix (Fin 2) (Fin 2) ℂ)) + B a
private theorem scalarB_hermitian (t : ℝ) (a : (EuclideanSpace ℝ (Fin 3))) : (scalarB t a).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [scalarB, B_formula, Complex.mul_re, Complex.mul_im]
private theorem scalarB_det (t : ℝ) (a : (EuclideanSpace ℝ (Fin 3))) :
    Matrix.det (scalarB t a) = ((t ^ 2 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
  rw [norm_sq_coords]
  apply Complex.ext <;>
    simp [scalarB, B_formula, Matrix.det_fin_two, Complex.mul_re, Complex.mul_im,
      pow_two] <;> ring
private theorem scalarB_norm_square (a : (EuclideanSpace ℝ (Fin 3))) :
    scalarB ‖a‖ a * scalarB ‖a‖ a =
      ((2 * ‖a‖ : ℝ) : ℂ) • scalarB ‖a‖ a := by
  have hs := norm_sq_coords a
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [scalarB, B_formula, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im] <;> nlinarith [hs]
theorem scalarB_posSemidef_iff (t : ℝ) (a : (EuclideanSpace ℝ (Fin 3))) :
    (scalarB t a).PosSemidef ↔ ‖a‖ ≤ t := by
  constructor
  · intro h
    have hd := (Complex.nonneg_iff.mp h.det_nonneg).1
    rw [scalarB_det] at hd
    simp only [Complex.ofReal_re] at hd
    have h0 := (Complex.nonneg_iff.mp (h.diag_nonneg (i := 0))).1
    have h1 := (Complex.nonneg_iff.mp (h.diag_nonneg (i := 1))).1
    simp [scalarB, B_formula] at h0 h1
    have ht : 0 ≤ t := by linarith
    nlinarith [norm_nonneg a]
  · intro h
    have hr := norm_nonneg a
    have hP : (scalarB ‖a‖ a).PosSemidef := by
      by_cases hz : ‖a‖ = 0
      · have ha : a = 0 := norm_eq_zero.mp hz
        simpa [scalarB, ha] using (Matrix.PosSemidef.zero : (0 : (Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef)
      · have hp : 0 < 2 * ‖a‖ := by positivity
        have hs := Matrix.posSemidef_conjTranspose_mul_self (scalarB ‖a‖ a)
        rw [(scalarB_hermitian ‖a‖ a).eq, scalarB_norm_square] at hs
        have hc : (0 : ℂ) ≤ (((2 * ‖a‖)⁻¹ : ℝ) : ℂ) := by
          exact_mod_cast inv_nonneg.mpr hp.le
        have hsc := hs.smul hc
        simpa only [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hp.ne',
          Complex.ofReal_one, one_smul] using hsc
    have hI : (((t - ‖a‖ : ℝ) : ℂ) • (1 : (Matrix (Fin 2) (Fin 2) ℂ))).PosSemidef :=
      Matrix.PosSemidef.one.smul (by exact_mod_cast sub_nonneg.mpr h)
    have heq : scalarB t a = ((t - ‖a‖ : ℝ) : ℂ) • (1 : (Matrix (Fin 2) (Fin 2) ℂ)) + scalarB ‖a‖ a := by
      ext i j
      simp [scalarB, sub_mul, add_mul]
      ring
    rw [heq]
    exact hI.add hP
theorem half_scalarB_posSemidef_iff (t : ℝ) (a : (EuclideanSpace ℝ (Fin 3))) :
    ((1 / 2 : ℂ) • scalarB t a).PosSemidef ↔ ‖a‖ ≤ t := by
  constructor
  · intro h
    have hs := h.smul (show (0 : ℂ) ≤ 2 by norm_num)
    have hh : (scalarB t a).PosSemidef := by
      have he : (2 : ℂ) * (1 / 2 : ℂ) = 1 := by norm_num
      simpa only [smul_smul, he, one_smul] using hs
    exact (scalarB_posSemidef_iff t a).mp hh
  · intro h
    exact ((scalarB_posSemidef_iff t a).mpr h).smul
      (by apply Complex.nonneg_iff.mpr; norm_num [Complex.div_re, Complex.div_im] :
        (0 : ℂ) ≤ 1 / 2)
private theorem hermitian_decomposition (A : (Matrix (Fin 2) (Fin 2) ℂ)) (h : A.IsHermitian) :
    A = scalarB ((Matrix.trace A).re / 2) (((1 / 2 : ℝ) • bloch A)) := by
  have hd0 := congrArg Complex.im (h.apply 0 0)
  have hd1 := congrArg Complex.im (h.apply 1 1)
  have hr01 := congrArg Complex.re (h.apply 1 0)
  have hi01 := congrArg Complex.im (h.apply 1 0)
  change -(A 0 0).im = (A 0 0).im at hd0
  change -(A 1 1).im = (A 1 1).im at hd1
  change (A 0 1).re = (A 1 0).re at hr01
  change -(A 0 1).im = (A 1 0).im at hi01
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [scalarB, B_formula, bloch, Matrix.trace, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im] <;> linarith
private theorem half_scalarB_double (t : ℝ) (a : (EuclideanSpace ℝ (Fin 3))) :
    (1 / 2 : ℂ) • scalarB (2 * t) ((2 : ℝ) • a) = scalarB t a := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [scalarB, B_formula, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im] <;> ring
private theorem half_scalarB_complement (t : ℝ) (a : (EuclideanSpace ℝ (Fin 3))) :
    (1 / 2 : ℂ) • scalarB (2 - t) (-a) =
      (1 : (Matrix (Fin 2) (Fin 2) ℂ)) - (1 / 2 : ℂ) • scalarB t a := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [scalarB, B_formula, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im] <;> ring
private theorem povm_bloch_coordinates (E : Bool → (Matrix (Fin 2) (Fin 2) ℂ)) (hE : IsPOVM E) :
    ∃ (α : ℝ) (a : (EuclideanSpace ℝ (Fin 3))),
      (∀ b, E b = (1 / 2 : ℂ) •
        scalarB (if b then α else 2 - α) (if b then a else -a)) ∧
      ‖a‖ ≤ α ∧ ‖a‖ ≤ 2 - α := by
  let α := (Matrix.trace (E true)).re
  let a := (2 : ℝ) • ((1 / 2 : ℝ) • bloch (E true))
  have ht : E true = (1 / 2 : ℂ) • scalarB α a := by
    have he := hermitian_decomposition (E true) (hE.1 true).isHermitian
    rw [← half_scalarB_double] at he
    have hα : 2 * ((Matrix.trace (E true)).re / 2) = α := by dsimp [α]; ring
    rw [hα] at he
    exact he
  have hs : E false + E true = 1 := by
    simpa [Fintype.sum_bool, add_comm] using hE.2
  have hf : E false = (1 / 2 : ℂ) • scalarB (2 - α) (-a) := by
    rw [half_scalarB_complement, ← ht]
    exact eq_sub_of_add_eq hs
  refine ⟨α, a, ?_, ?_, ?_⟩
  · intro b
    cases b
    · simpa using hf
    · simpa using ht
  · exact (half_scalarB_posSemidef_iff α a).mp (ht ▸ hE.1 true)
  · have hp := (half_scalarB_posSemidef_iff (2 - α) (-a)).mp (hf ▸ hE.1 false)
    simpa only [norm_neg] using hp
theorem endpoint_mem_Icc : endpoint ∈ Set.Icc (0 : ℝ) 1 := by
  have hs : 0 < Real.sqrt 13 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 13) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  constructor
  · exact div_nonneg (by norm_num) hs.le
  · apply (div_le_one hs).2
    nlinarith [Real.sqrt_nonneg 13]
private theorem parent_marginal_povm (J : ((Fin 4 → Bool) → Matrix (Fin 2) (Fin 2) ℂ)) (hJ : IsPOVM J) (i : Fin 4) :
    IsPOVM (fun b => ∑ ε with ε i = b, J ε) := by
  constructor
  · intro b
    exact Matrix.posSemidef_sum _ fun ε _ => hJ.1 ε
  · rw [Finset.sum_fiberwise]
    exact hJ.2
theorem compatible_of_parent {E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)} (J : ((Fin 4 → Bool) → Matrix (Fin 2) (Fin 2) ℂ)) (hJ : IsPOVM J)
    (hm : ∀ i b, E i b = ∑ ε with ε i = b, J ε) : Compatible4 E := by
  constructor
  · intro i
    have he : E i = fun b => ∑ ε with ε i = b, J ε := funext (hm i)
    rw [he]
    exact parent_marginal_povm J hJ i
  · exact ⟨J, hJ, hm⟩
namespace Decomposition
private def rep (ε : (Fin 3 → Bool)) (i : Fin 4) : Bool :=
  ![ε 0, ε 1, ε 2, true] i
private def Vlinear :
    PiLp 1 (fun _ : Fin 3 → Bool => EuclideanSpace ℝ (Fin 3)) →ₗ[ℝ]
      PiLp 2 (fun _ : Fin 4 => EuclideanSpace ℝ (Fin 3)) :=
  (WithLp.linearEquiv 2 ℝ (Fin 4 → EuclideanSpace ℝ (Fin 3))).symm.toLinearMap ∘ₗ
    LinearMap.pi (fun i => ∑ ε : Fin 3 → Bool, sgn (rep ε i) • PiLp.projₗ 1 (𝕜 := ℝ) (fun _ : Fin 3 → Bool => EuclideanSpace ℝ (Fin 3)) ε)
private theorem continuous_V : Continuous Vlinear := by
  letI : ContinuousSMul ℝ (PiLp 1 (fun _ : Fin 3 → Bool => EuclideanSpace ℝ (Fin 3))) :=
    IsBoundedSMul.continuousSMul
  letI : ContinuousSMul ℝ (PiLp 2 (fun _ : Fin 4 => EuclideanSpace ℝ (Fin 3))) :=
    IsBoundedSMul.continuousSMul
  exact Vlinear.continuous_of_finiteDimensional
private def imageBall : Set (PiLp 2 (fun _ : Fin 4 => EuclideanSpace ℝ (Fin 3))) := Vlinear '' (Metric.closedBall 0 1)
private theorem norm_input (b : (PiLp 1 (fun _ : Fin 3 → Bool => EuclideanSpace ℝ (Fin 3)))) : ‖b‖ = ∑ ε, ‖b ε‖ := by
  simpa using PiLp.norm_eq_sum (p := 1) (by norm_num) b
private theorem mem_budget (b : (PiLp 1 (fun _ : Fin 3 → Bool => EuclideanSpace ℝ (Fin 3)))) : b ∈ (Metric.closedBall 0 1) ↔ ∑ ε, ‖b ε‖ ≤ 1 := by
  simp [Metric.mem_closedBall, dist_eq_norm, norm_input]
private theorem budget_compact :
    IsCompact (Metric.closedBall (0 : PiLp 1 (fun _ : Fin 3 → Bool => EuclideanSpace ℝ (Fin 3))) 1) := isCompact_closedBall _ _
private theorem budget_convex :
    Convex ℝ (Metric.closedBall (0 : PiLp 1 (fun _ : Fin 3 → Bool => EuclideanSpace ℝ (Fin 3))) 1) := convex_closedBall 0 1
private theorem image_compact : IsCompact imageBall := budget_compact.image continuous_V
private theorem image_convex : Convex ℝ imageBall :=
  budget_convex.linear_image Vlinear
private theorem image_nonempty : imageBall.Nonempty := by
  refine ⟨0, 0, ?_, ?_⟩
  · simp
  · apply PiLp.ext
    intro i
    simp [Vlinear]
private theorem inner_V (X : (PiLp 2 (fun _ : Fin 4 => EuclideanSpace ℝ (Fin 3)))) (b : (PiLp 1 (fun _ : Fin 3 → Bool => EuclideanSpace ℝ (Fin 3)))) :
     inner ℝ X (Vlinear b) = ∑ ε, inner ℝ (signedSum (fun i => X i) (rep ε)) (b ε) := by
  change (∑ i, inner ℝ (X i) (∑ ε, sgn (rep ε i) • b ε)) = _
  simp only [inner_sum, real_inner_smul_right, signedSum, sum_inner, real_inner_smul_left]
  rw [Finset.sum_comm]
private def representative (δ : Fin 4 → Bool) : (Fin 3 → Bool) :=
  ![if δ 3 then δ 0 else !(δ 0),
    if δ 3 then δ 1 else !(δ 1),
    if δ 3 then δ 2 else !(δ 2)]
private theorem representative_sign (δ : Fin 4 → Bool) (i : Fin 4) :
     sgn (rep (representative δ) i) =
       sgn (δ 3) * sgn (δ i) := by
  fin_cases i
  · change sgn (if δ 3 then δ 0 else !(δ 0)) =
      sgn (δ 3) * sgn (δ 0)
    cases h0 : δ 0 <;> cases h3 : δ 3 <;>
      norm_num [sgn, h0, h3]
  · change sgn (if δ 3 then δ 1 else !(δ 1)) =
      sgn (δ 3) * sgn (δ 1)
    cases h1 : δ 1 <;> cases h3 : δ 3 <;>
      norm_num [sgn, h1, h3]
  · change sgn (if δ 3 then δ 2 else !(δ 2)) =
      sgn (δ 3) * sgn (δ 2)
    cases h2 : δ 2 <;> cases h3 : δ 3 <;>
      norm_num [sgn, h2, h3]
  · change (1 : ℝ) = sgn (δ 3) * sgn (δ 3)
    cases h3 : δ 3 <;> norm_num [sgn, h3]
private theorem norm_representative (X : (PiLp 2 (fun _ : Fin 4 => EuclideanSpace ℝ (Fin 3)))) (δ : Fin 4 → Bool) :
     ‖signedSum (fun i => X i) (rep (representative δ))‖ =
       ‖signedSum (fun i => X i) δ‖ := by
  have heq : signedSum (fun i => X i) (rep (representative δ)) =
      sgn (δ 3) • signedSum (fun i => X i) δ := by
    simp [signedSum, representative_sign,
      Finset.smul_sum, smul_smul]
  rw [heq, norm_smul]
  cases h : δ 3 <;> simp [sgn, h]
private theorem direction_norm_le (a : EuclideanSpace ℝ (Fin 3)) :
    ‖NormedSpace.normalize a‖ ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  · exact (NormedSpace.norm_normalize ha).le
private theorem inner_direction (a : (EuclideanSpace ℝ (Fin 3))) : inner ℝ a (NormedSpace.normalize a) = ‖a‖ := by
  by_cases ha : a = 0
  · simp [ha, NormedSpace.normalize]
  · have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    rw [NormedSpace.normalize, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
private def atom (X : (PiLp 2 (fun _ : Fin 4 => EuclideanSpace ℝ (Fin 3)))) (ε : (Fin 3 → Bool)) : (PiLp 1 (fun _ : Fin 3 → Bool => EuclideanSpace ℝ (Fin 3))) :=
  PiLp.single 1 ε (NormedSpace.normalize (signedSum (fun i => X i) (rep ε)))
private theorem atom_mem_budget (X : (PiLp 2 (fun _ : Fin 4 => EuclideanSpace ℝ (Fin 3)))) (ε : (Fin 3 → Bool)) : atom X ε ∈ (Metric.closedBall 0 1) := by
  change dist (atom X ε) 0 ≤ 1
  rw [dist_zero_right]
  exact (PiLp.norm_single 1 _ ε _).trans_le (direction_norm_le _)
private theorem atom_inner (X : (PiLp 2 (fun _ : Fin 4 => EuclideanSpace ℝ (Fin 3)))) (ε : (Fin 3 → Bool)) :
     inner ℝ X (Vlinear (atom X ε)) = ‖signedSum (fun i => X i) (rep ε)‖ := by
  rw [inner_V]
  classical
  simp [atom, PiLp.single_apply, apply_ite, inner_direction]
private theorem max_le_of_pairing_bound (X : (PiLp 2 (fun _ : Fin 4 => EuclideanSpace ℝ (Fin 3)))) (c : ℝ)
     (h : ∀ z ∈ imageBall, inner ℝ X z ≤ c) :
     maxNorm (fun i => X i) ≤ c := by
  apply Finset.sup'_le
  intro δ _
  rw [← norm_representative X δ, ← atom_inner]
  exact h _ ⟨atom X (representative δ), atom_mem_budget X _, rfl⟩
private theorem scale_nonneg : 0 ≤ endpoint := by unfold endpoint; positivity
private theorem scale_sharp (X : (PiLp 2 (fun _ : Fin 4 => EuclideanSpace ℝ (Fin 3)))) :
     endpoint * (∑ i, ‖X i‖) ≤ maxNorm (fun i => X i) := by
  have h := four_vector_inequality (fun i => X i)
  have hs : Real.sqrt 13 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hscale : endpoint * (Real.sqrt 13 / 2) = 1 := by
    unfold endpoint
    field_simp
  calc
    _ ≤ endpoint * ((Real.sqrt 13 / 2) * maxNorm (fun i => X i)) :=
      mul_le_mul_of_nonneg_left h scale_nonneg
    _ = maxNorm (fun i => X i) := by rw [← mul_assoc, hscale, one_mul]
private theorem target_pairing_le (n : Fin 4 → (EuclideanSpace ℝ (Fin 3))) (hn : ∀ i, ‖n i‖ ≤ 1) (X : (PiLp 2 (fun _ : Fin 4 => EuclideanSpace ℝ (Fin 3)))) :
     inner ℝ X (WithLp.toLp 2 (fun i => endpoint • n i) : (PiLp 2 (fun _ : Fin 4 => EuclideanSpace ℝ (Fin 3)))) ≤
       maxNorm (fun i => X i) := by
  change (∑ i, inner ℝ (X i) (endpoint • n i)) ≤ _
  simp only [real_inner_smul_right]
  rw [← Finset.mul_sum]
  apply le_trans _ (scale_sharp X)
  apply mul_le_mul_of_nonneg_left _ scale_nonneg
  apply Finset.sum_le_sum
  intro i _
  exact (real_inner_le_norm (X i) (n i)).trans
    ((mul_le_mul_of_nonneg_left (hn i) (norm_nonneg _)).trans_eq (mul_one _))
private theorem target_mem_image (n : Fin 4 → (EuclideanSpace ℝ (Fin 3))) (hn : ∀ i, ‖n i‖ ≤ 1) :
     (WithLp.toLp 2 (fun i => endpoint • n i) : (PiLp 2 (fun _ : Fin 4 => EuclideanSpace ℝ (Fin 3)))) ∈ imageBall := by
  let u : (PiLp 2 (fun _ : Fin 4 => EuclideanSpace ℝ (Fin 3))) := WithLp.toLp 2 (fun i => endpoint • n i)
  obtain ⟨v, hv, hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    image_nonempty image_compact.isComplete image_convex u
  have hproj := (norm_eq_iInf_iff_real_inner_le_zero image_convex hv).mp hmin
  have hbound : ∀ z ∈ imageBall, inner ℝ (u - v) z ≤ inner ℝ (u - v) v := by
    intro z hz
    have h := hproj z hz
    rw [inner_sub_right] at h
    linarith
  have hsharp := max_le_of_pairing_bound (u - v) _ hbound
  have htarget := target_pairing_le n hn (u - v)
  have hnorm : inner ℝ (u - v) (u - v) ≤ 0 := by
    rw [inner_sub_right]
    exact sub_nonpos.mpr (htarget.trans hsharp)
  have heq : u = v := by
    have hzero : ‖u - v‖ = 0 := by
      rw [real_inner_self_eq_norm_sq] at hnorm
      nlinarith [norm_nonneg (u - v)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  simpa only [← heq] using hv
private theorem sign_decomposition (n : Fin 4 → (EuclideanSpace ℝ (Fin 3))) (hn : ∀ i, ‖n i‖ ≤ 1) :
     ∃ b : (Fin 3 → Bool) → (EuclideanSpace ℝ (Fin 3)), (∑ ε, ‖b ε‖ ≤ 1) ∧
       ∀ i, ∑ ε, sgn (rep ε i) • b ε = (2 / Real.sqrt 13) • n i := by
  obtain ⟨b, hb, heq⟩ := target_mem_image n hn
  refine ⟨fun ε => b ε, (mem_budget b).mp hb, ?_⟩
  intro i
  exact congrArg (fun x : (PiLp 2 (fun _ : Fin 4 => EuclideanSpace ℝ (Fin 3))) => x i) heq
end Decomposition
namespace SignParent
open Decomposition
private def negRep (ε : (Fin 3 → Bool)) : (Fin 4 → Bool) := fun i => !(rep ε i)
private theorem representative_rep (ε : (Fin 3 → Bool)) : representative (rep ε) = ε := by
  funext j
  fin_cases j
  · change (if true then ε 0 else !(ε 0)) = ε 0
    rfl
  · change (if true then ε 1 else !(ε 1)) = ε 1
    rfl
  · change (if true then ε 2 else !(ε 2)) = ε 2
    rfl
private theorem representative_negRep (ε : (Fin 3 → Bool)) : representative (negRep ε) = ε := by
  funext j
  fin_cases j
  · change (if !true then !(ε 0) else !(!(ε 0))) = ε 0
    simp
  · change (if !true then !(ε 1) else !(!(ε 1))) = ε 1
    simp
  · change (if !true then !(ε 2) else !(!(ε 2))) = ε 2
    simp
private def pairEquiv : (Fin 3 → Bool) × Bool ≃ (Fin 4 → Bool) where
  toFun := fun p => if p.2 then rep p.1 else negRep p.1
  invFun := fun δ => (representative δ, δ 3)
  left_inv p := by
    rcases p with ⟨ε, f⟩
    cases f
    · simp [negRep, rep, representative_negRep]
    · simp [rep, representative_rep]
  right_inv δ := by
    change (if δ 3 then rep (representative δ) else negRep (representative δ)) = δ
    funext i
    simp only [ite_apply]
    fin_cases i
    · change (if δ 3 then (if δ 3 then δ 0 else !(δ 0))
        else !(if δ 3 then δ 0 else !(δ 0))) = δ 0
      cases h : δ 3 <;> simp [h]
    · change (if δ 3 then (if δ 3 then δ 1 else !(δ 1))
        else !(if δ 3 then δ 1 else !(δ 1))) = δ 1
      cases h : δ 3 <;> simp [h]
    · change (if δ 3 then (if δ 3 then δ 2 else !(δ 2))
        else !(if δ 3 then δ 2 else !(δ 2))) = δ 2
      cases h : δ 3 <;> simp [h]
    · change (if δ 3 then true else !true) = δ 3
      cases h : δ 3 <;> rfl
private theorem sum_antipodal {A : Type*} [AddCommMonoid A] (f : (Fin 4 → Bool) → A) :
     ∑ δ, f δ = ∑ ε : (Fin 3 → Bool), (f (rep ε) + f (negRep ε)) := by
  classical
  rw [← Equiv.sum_comp pairEquiv]
  rw [Fintype.sum_prod_type]
  simp [pairEquiv, Fintype.sum_bool]
private theorem sign_not (b : Bool) : sgn (!b) = -sgn b := by
  cases b <;> norm_num [sgn]
private def p (b : (Fin 3 → Bool) → (EuclideanSpace ℝ (Fin 3))) (ε : (Fin 3 → Bool)) : ℝ :=
  ‖b ε‖ + (1 - ∑ η, ‖b η‖) / 8
private theorem p_ge_norm (b : (Fin 3 → Bool) → (EuclideanSpace ℝ (Fin 3))) (hb : ∑ ε, ‖b ε‖ ≤ 1) (ε : (Fin 3 → Bool)) :
     ‖b ε‖ ≤ p b ε := by
  unfold p
  linarith
private theorem sum_p (b : (Fin 3 → Bool) → (EuclideanSpace ℝ (Fin 3))) : ∑ ε, p b ε = 1 := by
  simp only [p, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ]
  have hc : Fintype.card (Fin 3 → Bool) = 8 := by norm_num
  rw [hc]
  ring
private def t (b : (Fin 3 → Bool) → (EuclideanSpace ℝ (Fin 3))) (δ : (Fin 4 → Bool)) : ℝ := p b (representative δ) / 2
private def a (b : (Fin 3 → Bool) → (EuclideanSpace ℝ (Fin 3))) (δ : (Fin 4 → Bool)) : (EuclideanSpace ℝ (Fin 3)) :=
  (sgn (δ 3) / 2) • b (representative δ)
private theorem t_rep (b : (Fin 3 → Bool) → (EuclideanSpace ℝ (Fin 3))) (ε : (Fin 3 → Bool)) : t b (rep ε) = p b ε / 2 := by
  simp [t, representative_rep]
private theorem t_negRep (b : (Fin 3 → Bool) → (EuclideanSpace ℝ (Fin 3))) (ε : (Fin 3 → Bool)) : t b (negRep ε) = p b ε / 2 := by
  simp [t, representative_negRep]
private theorem a_rep (b : (Fin 3 → Bool) → (EuclideanSpace ℝ (Fin 3))) (ε : (Fin 3 → Bool)) : a b (rep ε) = (1 / 2 : ℝ) • b ε := by
  simp [a, representative_rep, rep, sgn]
private theorem a_negRep (b : (Fin 3 → Bool) → (EuclideanSpace ℝ (Fin 3))) (ε : (Fin 3 → Bool)) : a b (negRep ε) = (-1 / 2 : ℝ) • b ε := by
  simp [a, representative_negRep, negRep, rep, sgn]
private theorem norm_a_le_t (b : (Fin 3 → Bool) → (EuclideanSpace ℝ (Fin 3))) (hb : ∑ ε, ‖b ε‖ ≤ 1) (δ : (Fin 4 → Bool)) :
     ‖a b δ‖ ≤ t b δ := by
  have h := p_ge_norm b hb (representative δ)
  unfold a t
  rw [norm_smul]
  cases hδ : δ 3 <;> simp [sgn, hδ] <;> linarith
private theorem sum_t (b : (Fin 3 → Bool) → (EuclideanSpace ℝ (Fin 3))) : ∑ δ, t b δ = 1 := by
  rw [sum_antipodal]
  simp only [t_rep, t_negRep]
  simp_rw [show ∀ x : ℝ, x / 2 + x / 2 = x by intro x; ring]
  exact sum_p b
private theorem sum_a (b : (Fin 3 → Bool) → (EuclideanSpace ℝ (Fin 3))) : ∑ δ, a b δ = 0 := by
  rw [sum_antipodal]
  simp only [a_rep, a_negRep, ← add_smul]
  norm_num
private theorem signed_sum_t (b : (Fin 3 → Bool) → (EuclideanSpace ℝ (Fin 3))) (i : Fin 4) :
     ∑ δ, sgn (δ i) * t b δ = 0 := by
  rw [sum_antipodal]
  simp only [t_rep, t_negRep, negRep, sign_not]
  simp_rw [show ∀ x y : ℝ, x * y + -x * y = 0 by intros; ring]
  simp
private theorem signed_sum_a (b : (Fin 3 → Bool) → (EuclideanSpace ℝ (Fin 3))) (i : Fin 4) :
     ∑ δ, sgn (δ i) • a b δ =
       ∑ ε, sgn (rep ε i) • b ε := by
  rw [sum_antipodal]
  simp only [a_rep, a_negRep, negRep, sign_not, smul_smul, ← add_smul]
  congr 1
  funext ε
  congr 1
  ring
private theorem parent_data (n : Fin 4 → (EuclideanSpace ℝ (Fin 3))) (hn : ∀ i, ‖n i‖ ≤ 1) :
     ∃ t : (Fin 4 → Bool) → ℝ, ∃ a : (Fin 4 → Bool) → (EuclideanSpace ℝ (Fin 3)),
       (∀ δ, ‖a δ‖ ≤ t δ) ∧ (∑ δ, t δ = 1) ∧ (∑ δ, a δ = 0) ∧
       (∀ i, ∑ δ, sgn (δ i) * t δ = 0) ∧
       (∀ i, ∑ δ, sgn (δ i) • a δ = (2 / Real.sqrt 13) • n i) := by
  obtain ⟨b, hb, hbn⟩ := sign_decomposition n hn
  refine ⟨t b, a b, norm_a_le_t b hb, sum_t b, sum_a b, signed_sum_t b, ?_⟩
  intro i
  exact (signed_sum_a b i).trans (hbn i)
end SignParent
private def unbiased (n : Fin 4 → (EuclideanSpace ℝ (Fin 3))) : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ) := fun i b =>
  (1 / 2 : ℂ) • scalarB 1 (sgn b • n i)
private theorem scalarB_sum {ι : Type*} (s : Finset ι) (t : ι → ℝ) (a : ι → (EuclideanSpace ℝ (Fin 3))) :
     scalarB (∑ j ∈ s, t j) (∑ j ∈ s, a j) = ∑ j ∈ s, scalarB (t j) (a j) := by
  simp only [scalarB, Complex.ofReal_sum, Finset.sum_smul, B_sum, Finset.sum_add_distrib]
private theorem scalarB_real_smul (r t : ℝ) (a : (EuclideanSpace ℝ (Fin 3))) :
     scalarB (r * t) (r • a) = r • scalarB t a := by
  calc
    _ = ((r : ℂ) * (t : ℂ)) • (1 : (Matrix (Fin 2) (Fin 2) ℂ)) + (r : ℂ) • B a := by
      rw [scalarB, B_smul, Complex.ofReal_mul]
    _ = (r : ℂ) • scalarB t a := by simp only [scalarB, smul_add, smul_smul]
    _ = r • scalarB t a :=
      (RCLike.real_smul_eq_coe_smul (K := ℂ) r (scalarB t a)).symm
private theorem noisy_unbiased_formula (s : ℝ) (n : Fin 4 → (EuclideanSpace ℝ (Fin 3))) (i : Fin 4) (b : Bool) :
     noisy s (unbiased n) i b = (1 / 2 : ℝ) •
       ((1 : (Matrix (Fin 2) (Fin 2) ℂ)) + sgn b • (s • B (n i))) := by
  ext j k
  simp [noisy, unbiased, scalarB, B_smul, RCLike.real_smul_eq_coe_smul,
    Complex.real_smul, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring
private theorem signed_parent_marginal (J : ((Fin 4 → Bool) → Matrix (Fin 2) (Fin 2) ℂ)) (hsum : ∑ δ, J δ = 1)
     (D : Fin 4 → (Matrix (Fin 2) (Fin 2) ℂ)) (hD : ∀ i, ∑ δ, sgn (δ i) • J δ = D i)
     (i : Fin 4) (b : Bool) :
     (∑ δ with δ i = b, J δ) = (1 / 2 : ℝ) • ((1 : (Matrix (Fin 2) (Fin 2) ℂ)) + sgn b • D i) := by
  classical
  have heach (δ : (Fin 4 → Bool)) :
      (if δ i = b then (2 : ℝ) • J δ else 0) =
        J δ + sgn b • (sgn (δ i) • J δ) := by
    cases hδ : δ i <;> cases b <;>
      simp [sgn, hδ, two_smul]
  have htwo : (2 : ℝ) • (∑ δ with δ i = b, J δ) =
      (1 : (Matrix (Fin 2) (Fin 2) ℂ)) + sgn b • D i := by
    calc
      _ = ∑ δ, if δ i = b then (2 : ℝ) • J δ else 0 := by
        rw [Finset.smul_sum, Finset.sum_filter]
      _ = ∑ δ, (J δ + sgn b • (sgn (δ i) • J δ)) :=
        Finset.sum_congr rfl fun δ _ => heach δ
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.smul_sum, hsum, hD]
  calc
    _ = (1 / 2 : ℝ) • ((2 : ℝ) • (∑ δ with δ i = b, J δ)) := by
      simp [smul_smul]
    _ = _ := congrArg ((1 / 2 : ℝ) • ·) htwo
private theorem unbiased_parent (n : Fin 4 → (EuclideanSpace ℝ (Fin 3))) (hn : ∀ i, ‖n i‖ ≤ 1) :
     ∃ J : ((Fin 4 → Bool) → Matrix (Fin 2) (Fin 2) ℂ), IsPOVM J ∧
       ∀ i b, noisy endpoint (unbiased n) i b = ∑ δ with δ i = b, J δ := by
  obtain ⟨t, a, hpos, ht, ha, hts, has⟩ := SignParent.parent_data n hn
  let J : ((Fin 4 → Bool) → Matrix (Fin 2) (Fin 2) ℂ) := fun δ => scalarB (t δ) (a δ)
  have hJ : IsPOVM J := by
    constructor
    · intro δ
      exact (scalarB_posSemidef_iff _ _).mpr (hpos δ)
    · change ∑ δ, scalarB (t δ) (a δ) = 1
      rw [← scalarB_sum, ht, ha]
      simp [scalarB]
  have hsign (i : Fin 4) : ∑ δ, sgn (δ i) • J δ = endpoint • B (n i) := by
    change ∑ δ, sgn (δ i) • scalarB (t δ) (a δ) = _
    simp_rw [← scalarB_real_smul]
    rw [← scalarB_sum, hts, has]
    rw [show (2 / Real.sqrt 13 : ℝ) = endpoint by rfl]
    simp only [scalarB, Complex.ofReal_zero, zero_smul, zero_add, B_real_smul]
  refine ⟨J, hJ, ?_⟩
  intro i b
  rw [noisy_unbiased_formula]
  exact (signed_parent_marginal J hJ.2 (fun i => endpoint • B (n i)) hsign i b).symm
private theorem unbiased_compatible (n : Fin 4 → (EuclideanSpace ℝ (Fin 3))) (hn : ∀ i, ‖n i‖ ≤ 1) :
     Compatible4 (noisy endpoint (unbiased n)) := by
  obtain ⟨J, hJ, hm⟩ := unbiased_parent n hn
  exact compatible_of_parent J hJ hm
private def channelWeight (T : Fin 4 → Bool → Bool → ℝ) (δ η : (Fin 4 → Bool)) : ℝ :=
  ∏ i, T i (δ i) (η i)
private def postParent (T : Fin 4 → Bool → Bool → ℝ) (J : ((Fin 4 → Bool) → Matrix (Fin 2) (Fin 2) ℂ)) : ((Fin 4 → Bool) → Matrix (Fin 2) (Fin 2) ℂ) :=
  fun δ => ∑ η, channelWeight T δ η • J η
private theorem channelWeight_nonneg (T : Fin 4 → Bool → Bool → ℝ)
    (hT : ∀ i b c, 0 ≤ T i b c) (δ η : (Fin 4 → Bool)) : 0 ≤ channelWeight T δ η := by
  exact Finset.prod_nonneg (fun i _ => hT i (δ i) (η i))
private theorem channelWeight_sum (T : Fin 4 → Bool → Bool → ℝ)
    (hT : ∀ i c, ∑ b, T i b c = 1) (η : (Fin 4 → Bool)) :
    ∑ δ, channelWeight T δ η = 1 := by
  classical
  unfold channelWeight
  rw [← Fintype.prod_sum (fun (i : Fin 4) (b : Bool) => T i b (η i))]
  simp only [hT, Finset.prod_const_one]
private theorem channelWeight_marginal (T : Fin 4 → Bool → Bool → ℝ)
    (hT : ∀ i c, ∑ b, T i b c = 1) (η : (Fin 4 → Bool)) (i : Fin 4) (b : Bool) :
    (∑ δ with δ i = b, channelWeight T δ η) = T i b (η i) := by
  classical
  let f : Fin 4 → Bool → ℝ := fun j c =>
    if j = i then (if c = b then T j c (η j) else 0) else T j c (η j)
  have hf : ∀ δ : (Fin 4 → Bool), (if δ i = b then channelWeight T δ η else 0) =
      ∏ j, f j (δ j) := by
    intro δ
    by_cases hb : δ i = b
    · rw [if_pos hb]
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j = i
      · subst j
        simp [f,hb]
      · simp [f,hj]
    · rw [if_neg hb]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [f,hb]
  have hfs : ∀ j, (∑ c, f j c) = if j = i then T j b (η j) else 1 := by
    intro j
    by_cases hj : j = i
    · subst j
      cases b <;> simp [f]
    · simp only [f, if_neg hj]
      rw [hT]
  simp only [Finset.sum_filter]
  simp_rw [hf]
  rw [← Fintype.prod_sum]
  simp_rw [hfs]
  simp
private theorem postParent_povm (T : Fin 4 → Bool → Bool → ℝ)
    (hT0 : ∀ i b c, 0 ≤ T i b c) (hT1 : ∀ i c, ∑ b, T i b c = 1)
    (J : ((Fin 4 → Bool) → Matrix (Fin 2) (Fin 2) ℂ)) (hJ : IsPOVM J) : IsPOVM (postParent T J) := by
  classical
  refine ⟨fun δ => ?_, ?_⟩
  · apply Matrix.posSemidef_sum
    intro η _
    exact (hJ.1 η).smul (channelWeight_nonneg T hT0 δ η)
  · change (∑ δ, ∑ η, channelWeight T δ η • J η) = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, channelWeight_sum T hT1, one_smul]
    exact hJ.2
private theorem postParent_marginal (T : Fin 4 → Bool → Bool → ℝ)
    (hT1 : ∀ i c, ∑ b, T i b c = 1) (J : ((Fin 4 → Bool) → Matrix (Fin 2) (Fin 2) ℂ)) (i : Fin 4) (b : Bool) :
    (∑ δ with δ i = b, postParent T J δ) = ∑ η, T i b (η i) • J η := by
  classical
  unfold postParent
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, channelWeight_marginal T hT1]
private def direction (a : (EuclideanSpace ℝ (Fin 3))) : (EuclideanSpace ℝ (Fin 3)) :=
  if ‖a‖ = 0 then (EuclideanSpace.single 0 (1 : ℝ)) else NormedSpace.normalize a
private theorem direction_norm (a : (EuclideanSpace ℝ (Fin 3))) : ‖direction a‖ = 1 := by
  by_cases hz : ‖a‖ = 0
  · simp [direction, NormedSpace.normalize, hz, PiLp.norm_single]
  · simp [direction, NormedSpace.normalize, hz, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg a), inv_mul_cancel₀ hz]
private theorem norm_smul_direction (a : EuclideanSpace ℝ (Fin 3)) :
    ‖a‖ • direction a = a := by
  by_cases ha : a = 0
  · simp [direction, ha]
  · simpa [direction, ha] using NormedSpace.norm_smul_normalize a
private def wI (α : ℝ) (a : (EuclideanSpace ℝ (Fin 3))) : ℝ := (α - ‖a‖) / 2
private def w0 (α : ℝ) (a : (EuclideanSpace ℝ (Fin 3))) : ℝ := (2 - α - ‖a‖) / 2
private theorem weights_nonneg (α : ℝ) (a : (EuclideanSpace ℝ (Fin 3))) (ha : ‖a‖ ≤ α) (hb : ‖a‖ ≤ 2 - α) :
    0 ≤ ‖a‖ ∧ 0 ≤ wI α a ∧ 0 ≤ w0 α a := by
  dsimp [wI, w0]
  constructor
  · exact norm_nonneg _
  constructor <;> linarith
private theorem weights_sum (α : ℝ) (a : (EuclideanSpace ℝ (Fin 3))) : ‖a‖ + wI α a + w0 α a = 1 := by
  dsimp [wI, w0]
  ring
private def biasChannel (s ρ u v : ℝ) (b c : Bool) : ℝ :=
  ρ * (if b = c then 1 else 0) +
    u * (1 + sgn b * s) / 2 + v * (1 - sgn b * s) / 2
private theorem biasChannel_nonneg (s ρ u v : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hρ : 0 ≤ ρ) (hu : 0 ≤ u) (hv : 0 ≤ v) (b c : Bool) :
    0 ≤ biasChannel s ρ u v b c := by
  have hp : 0 ≤ 1 + s := by linarith [hs.1]
  have hm : 0 ≤ 1 - s := by linarith [hs.2]
  cases b <;> cases c <;> simp [biasChannel, sgn]
  all_goals nlinarith [mul_nonneg hu hp, mul_nonneg hu hm,
    mul_nonneg hv hp, mul_nonneg hv hm]
private theorem biasChannel_sum (s ρ u v : ℝ) (hw : ρ + u + v = 1) (c : Bool) :
    ∑ b, biasChannel s ρ u v b c = 1 := by
  cases c <;> simp [Fintype.sum_bool, biasChannel, sgn]
  all_goals nlinarith only [hw]
private theorem noisy_povm (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) (hE : ∀ i, IsPOVM (E i)) (i : Fin 4) : IsPOVM (noisy s E i) := by
  have hhalf : ((1 / 2 : ℂ) • (1 : (Matrix (Fin 2) (Fin 2) ℂ))).PosSemidef := by
    simpa [scalarB] using
      ((half_scalarB_posSemidef_iff 1 (0 : (EuclideanSpace ℝ (Fin 3)))).mpr (by simp))
  refine ⟨fun b => ((hE i).1 b).smul hs.1 |>.add (hhalf.smul (sub_nonneg.mpr hs.2)), ?_⟩
  have he : E i true + E i false = 1 := by
    simpa [Fintype.sum_bool] using (hE i).2
  change ∑ b, (s • E i b + (1 - s) • ((1 / 2 : ℂ) • (1 : (Matrix (Fin 2) (Fin 2) ℂ)))) = 1
  rw [Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [(hE i).2]
  simp only [Fintype.sum_bool]
  ext k l
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im] <;> ring
private theorem biasChannel_parent_sum (s ρ u v : ℝ) (J : ((Fin 4 → Bool) → Matrix (Fin 2) (Fin 2) ℂ)) (i : Fin 4) (b : Bool) :
    (∑ η, biasChannel s ρ u v b (η i) • J η) =
      ρ • (∑ η with η i = b, J η) +
        (u * (1 + sgn b * s) / 2 +
          v * (1 - sgn b * s) / 2) • (∑ η, J η) := by
  classical
  have hfirst : (∑ η : (Fin 4 → Bool), (ρ * (if b = η i then 1 else 0)) • J η) =
      ρ • (∑ η with η i = b, J η) := by
    rw [Finset.smul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro η _
    by_cases h : η i = b
    · simp [h]
    · have h' : b ≠ η i := Ne.symm h
      simp [h, h']
  simp only [biasChannel, add_smul, Finset.sum_add_distrib]
  rw [hfirst]
  simp only [← Finset.smul_sum, add_assoc]
private theorem weighted_noisy_unbiased (s : ℝ) (a : (EuclideanSpace ℝ (Fin 3))) (n : Fin 4 → (EuclideanSpace ℝ (Fin 3)))
    (i : Fin 4) (h : ‖a‖ • n i = a) (b : Bool) :
    ‖a‖ • noisy s (unbiased n) i b =
      (1 / 2 : ℝ) • (‖a‖ • (1 : (Matrix (Fin 2) (Fin 2) ℂ)) + sgn b • (s • B a)) := by
  have hB : ‖a‖ • B (n i) = B a := by rw [← B_real_smul, h]
  rw [noisy_unbiased_formula]
  rw [smul_comm ‖a‖ (1 / 2 : ℝ), smul_add,
    smul_comm ‖a‖ (sgn b), smul_comm ‖a‖ s, hB]
private theorem bias_noise_identity (s α : ℝ) (a : (EuclideanSpace ℝ (Fin 3))) (n : Fin 4 → (EuclideanSpace ℝ (Fin 3)))
    (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) (i : Fin 4)
    (he : ∀ b, E i b = (1 / 2 : ℂ) •
      scalarB (if b then α else 2 - α) (if b then a else -a))
    (hn : ‖a‖ • n i = a) (b : Bool) :
    ‖a‖ • noisy s (unbiased n) i b +
      (wI α a * (1 + sgn b * s) / 2 +
        w0 α a * (1 - sgn b * s) / 2) • (1 : (Matrix (Fin 2) (Fin 2) ℂ)) =
          noisy s E i b := by
  rw [weighted_noisy_unbiased s a n i hn b]
  simp only [noisy, he]
  cases b <;> ext j k <;> fin_cases j <;> fin_cases k <;> apply Complex.ext <;>
    simp [wI, w0, sgn, scalarB, B_formula,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring
theorem all_povms_compatible (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) (hE : ∀ i, IsPOVM (E i)) :
    Compatible4 (noisy endpoint E) := by
  classical
  choose α a he ha hb using fun i => povm_bloch_coordinates (E i) (hE i)
  let n : Fin 4 → (EuclideanSpace ℝ (Fin 3)) := fun i => direction (a i)
  have hn : ∀ i, ‖n i‖ ≤ 1 := fun i => (direction_norm (a i)).le
  obtain ⟨_, J, hJ, hm⟩ := unbiased_compatible n hn
  let T : Fin 4 → Bool → Bool → ℝ :=
    fun i => biasChannel endpoint (‖a i‖) (wI (α i) (a i)) (w0 (α i) (a i))
  have hT0 : ∀ i b c, 0 ≤ T i b c := by
    intro i b c
    have hw := weights_nonneg (α i) (a i) (ha i) (hb i)
    exact biasChannel_nonneg endpoint _ _ _ endpoint_mem_Icc hw.1 hw.2.1 hw.2.2 b c
  have hT1 : ∀ i c, ∑ b, T i b c = 1 := by
    intro i c
    exact biasChannel_sum endpoint _ _ _ (weights_sum (α i) (a i)) c
  refine ⟨noisy_povm endpoint endpoint_mem_Icc E hE, postParent T J,
    postParent_povm T hT0 hT1 J hJ, ?_⟩
  intro i b
  rw [postParent_marginal T hT1 J i b]
  change noisy endpoint E i b =
    ∑ η, biasChannel endpoint (‖a i‖) (wI (α i) (a i)) (w0 (α i) (a i)) b (η i) • J η
  rw [biasChannel_parent_sum, ← hm i b, hJ.2]
  exact (bias_noise_identity endpoint (α i) (a i) n E i (he i)
    (norm_smul_direction (a i)) b).symm
end D5.S3.Quantum.Measurement.FourQubitParentConstruction
