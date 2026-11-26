/- GID: D5/S3/Quantum/Divergence/AlphaZAffine/Result
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/AlphaZAffine/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Affine Renyi monotonicity including Umegaki and supported semidefinite inputs. -/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic
import D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormExterior
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import D5.S3.Quantum.Schatten.PowerMajorization
import Mathlib.Analysis.MeanInequalities
import D5.S3.Quantum.Schatten.Holder
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Deriv
import D5.S3.Quantum.Hiai.SupportPowerLimits
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
noncomputable section
namespace D5.S3.Quantum.Divergence.AlphaZAffine
section ParametersParts
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open _root_.Matrix
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩
def affineZ (κ z₀ α : ℝ) : ℝ := κ * α + z₀
def renyiProduct (ρ σ : Matrix d d ℂ) (α z : ℝ) : Matrix d d ℂ :=
  ρ ^ (α / (2 * z)) * σ ^ ((1 - α) / (2 * z))
private lemma rpow_rpow_all {A : Matrix d d ℂ} (hA : A.PosDef) (x y : ℝ) :
    (A ^ x) ^ y = A ^ (x * y) := by
  by_cases hx : x = 0
  · subst x
    simp only [CFC.rpow_zero _ hA.posSemidef.nonneg, zero_mul]
    exact CFC.one_rpow
  · exact CFC.rpow_rpow A x y hx hA.isStrictlyPositive
end ParametersParts
section TraceParts
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open _root_.Matrix
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩
def traceMoment (X : Matrix d d ℂ) (z : ℝ) : ℝ :=
  (Matrix.trace ((Xᴴ * X) ^ z)).re
def renyiQ (ρ σ : Matrix d d ℂ) (α z : ℝ) : ℝ :=
  traceMoment (renyiProduct ρ σ α z) z
def renyiD (ρ σ : Matrix d d ℂ) (α z : ℝ) : ℝ :=
  Real.log (renyiQ ρ σ α z / (Matrix.trace ρ).re) / (α - 1)
private theorem renyiProduct_isUnit {ρ σ : Matrix d d ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (α z : ℝ) : IsUnit (renyiProduct ρ σ α z) :=
  (hρ.isStrictlyPositive.rpow ρ _).isUnit.mul
    (hσ.isStrictlyPositive.rpow σ _).isUnit
private theorem traceMoment_pos [Nonempty d] {X : Matrix d d ℂ} (hX : IsUnit X) (z : ℝ) :
    0 < traceMoment X z := by
  have hg : (Xᴴ * X).PosDef := by
    simpa only [Matrix.star_eq_conjTranspose, mul_one] using
      (hX.posDef_star_left_conjugate_iff (x := (1 : Matrix d d ℂ))).mpr
      (show (1 : Matrix d d ℂ).PosDef from Matrix.PosDef.one)
  have ht := ((hg.isStrictlyPositive.rpow _ z).posDef).trace_pos
  exact ht.1
private theorem renyiQ_pos [Nonempty d] {ρ σ : Matrix d d ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (α z : ℝ) : 0 < renyiQ ρ σ α z :=
  traceMoment_pos (renyiProduct_isUnit hρ hσ α z) z
private theorem renyiQ_one {ρ σ : Matrix d d ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {z : ℝ} (hz : z ≠ 0) : renyiQ ρ σ 1 z = (Matrix.trace ρ).re := by
  have hp : renyiProduct ρ σ 1 z = ρ ^ (1 / (2 * z)) := by
    simp [renyiProduct, CFC.rpow_zero _ hσ.posSemidef.nonneg]
  have hs : (ρ ^ (1 / (2 * z)) : Matrix d d ℂ)ᴴ = ρ ^ (1 / (2 * z)) :=
    (hρ.isStrictlyPositive.rpow ρ _).isSelfAdjoint.star_eq
  unfold renyiQ traceMoment
  rw [hp, hs, ← CFC.rpow_add hρ.isUnit, rpow_rpow_all hρ]
  have he : (1 / (2 * z) + 1 / (2 * z)) * z = 1 := by field_simp; ring
  rw [he, CFC.rpow_one ρ hρ.posSemidef.nonneg]
end TraceParts
section ThreeLinesParts
open NormedSpace Complex Set
variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [StarRing E]
  [CStarRing E] [CompleteSpace E] [StarModule ℂ E]
local instance : NormedAlgebra ℚ E := .restrictScalars ℚ ℂ E
private def expSandwich (H K X : E) (w : ℂ) : E :=
  exp (w • H) * X * exp (w • K)
private lemma imaginary_exp_unitary {H : E} (hH : IsSelfAdjoint H) (s : ℝ) :
    exp (((s : ℂ) * I) • H) ∈ unitary E := by
  apply exp_mem_unitary_of_mem_skewAdjoint
  exact hH.smul_mem_skewAdjoint (by
    rw [skewAdjoint.mem_iff]
    simp)
private lemma expSandwich_split (H K X : E) (w : ℂ) :
    expSandwich H K X w = exp (((w.im : ℂ) * I) • H) *
      expSandwich H K X w.re * exp (((w.im : ℂ) * I) • K) := by
  have hsplitH : exp (w • H) =
      exp (((w.im : ℂ) * I) • H) * exp ((w.re : ℂ) • H) := by
    rw [← exp_add_of_commute (((Commute.refl H).smul_left _).smul_right _), ← add_smul]
    congr 2
    exact (Complex.re_add_im w).symm.trans (add_comm _ _)
  have hsplitK : exp (w • K) =
      exp ((w.re : ℂ) • K) * exp (((w.im : ℂ) * I) • K) := by
    rw [← exp_add_of_commute (((Commute.refl K).smul_left _).smul_right _), ← add_smul]
    rw [Complex.re_add_im]
  simp only [expSandwich, hsplitH, hsplitK, mul_assoc]
end ThreeLinesParts
section CompoundThreeLinesParts
open _root_.Matrix NormedSpace Complex Set
open scoped Matrix.Norms.L2Operator
open D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormExterior
variable {d : Type*} [Fintype d] [DecidableEq d]
private lemma compound_differentiable (H K X : Matrix d d ℂ) (k : ℕ) :
    Differentiable ℂ (fun w : ℂ => compoundMatrix (expSandwich H K X w) k) := by
  unfold compoundMatrix
  simp only [Matrix.det_apply']
  unfold expSandwich Matrix.submatrix
  simp only [Matrix.of_apply]
  fun_prop
private lemma compound_norm_re {H K : Matrix d d ℂ}
    (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) (X : Matrix d d ℂ) (k : ℕ) (w : ℂ) :
    ‖compoundMatrix (expSandwich H K X w) k‖ =
      ‖compoundMatrix (expSandwich H K X w.re) k‖ := by
  rw [expSandwich_split, compoundMatrix_mul, compoundMatrix_mul]
  rw [CStarRing.norm_mul_mem_unitary _
      (compoundMatrix_unitary _ (imaginary_exp_unitary hK w.im) k),
    CStarRing.norm_mem_unitary_mul _
      (compoundMatrix_unitary _ (imaginary_exp_unitary hH w.im) k)]
private theorem compound_expSandwich_three_lines {H K : Matrix d d ℂ}
    (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) (X : Matrix d d ℂ)
    (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖compoundMatrix (expSandwich H K X (t : ℂ)) k‖ ≤
      ‖compoundMatrix X k‖ ^ (1 - t) *
        ‖compoundMatrix (expSandwich H K X 1) k‖ ^ t := by
  let F := fun w : ℂ => compoundMatrix (expSandwich H K X w) k
  have hd : Differentiable ℂ F := compound_differentiable H K X k
  have hc : Continuous (fun s : ℝ => ‖F (s : ℂ)‖) :=
    (hd.continuous.comp Complex.continuous_ofReal).norm
  have hb : BddAbove ((norm ∘ F) '' HadamardThreeLines.verticalClosedStrip 0 1) := by
    obtain ⟨M, hM⟩ := (isCompact_Icc.image hc).bddAbove
    refine ⟨M, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    change ‖compoundMatrix (expSandwich H K X w) k‖ ≤ M
    rw [compound_norm_re hH hK]
    exact hM (mem_image_of_mem _ hw)
  apply HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' F
    (by simpa [HadamardThreeLines.verticalClosedStrip] using ht) hd.diffContOnCl hb
  · intro w hw
    change ‖compoundMatrix (expSandwich H K X w) k‖ ≤ _
    rw [compound_norm_re hH hK]
    have hw0 : w.re = 0 := hw
    simp [hw0, expSandwich]
  · intro w hw
    change ‖compoundMatrix (expSandwich H K X w) k‖ ≤ _
    rw [compound_norm_re hH hK]
    have hw1 : w.re = 1 := hw
    simp [hw1]
private theorem expSandwich_weak_log_majorization {H K : Matrix d d ℂ}
    (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) (X : Matrix d d ℂ)
    (k : ℕ) (hk : k ≤ Fintype.card d) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∏ i : Fin k, singularValuesSorted (expSandwich H K X (t : ℂ)) ⟨i.val, by omega⟩) ≤
      (∏ i : Fin k, singularValuesSorted X ⟨i.val, by omega⟩) ^ (1 - t) *
        (∏ i : Fin k, singularValuesSorted (expSandwich H K X 1) ⟨i.val, by omega⟩) ^ t := by
  have hn : 0 < Fintype.card {S : Finset d // S.card = k} := by
    simpa [Fintype.card_subtype] using Nat.choose_pos hk
  simpa only [complex_opNorm_sorted _ hn, ← prod_singularValuesSorted_eq_compoundSV _ k hk]
    using compound_expSandwich_three_lines hH hK X k ht
end CompoundThreeLinesParts
section PowerInterpolationParts
open _root_.Matrix NormedSpace
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩
local instance : NormedAlgebra ℚ (Matrix d d ℂ) := .restrictScalars ℚ ℂ _
private theorem exp_smul_log {A : Matrix d d ℂ} (hA : A.PosDef) (r : ℝ) :
    exp ((r : ℂ) • CFC.log A) = A ^ r := by
  have hlog : IsSelfAdjoint (CFC.log A) := IsSelfAdjoint.log
  have hscaled : IsSelfAdjoint (r • CFC.log A) := (IsSelfAdjoint.all r).smul hlog
  have hc : ContinuousOn Real.log (spectrum ℝ A) :=
    Real.continuousOn_log.mono (fun x hx => (hA.isStrictlyPositive.spectrum_pos hx).ne')
  rw [Complex.coe_smul, ← CFC.real_exp_eq_normedSpace_exp hscaled, CFC.log,
    ← cfc_const_mul r Real.log A hc]
  calc
    cfc Real.exp (cfc (fun x : ℝ => r * Real.log x) A) =
        cfc (fun x : ℝ => Real.exp (r * Real.log x)) A :=
      (cfc_comp Real.exp (fun x : ℝ => r * Real.log x) A
        hA.isHermitian (by fun_prop) (continuousOn_const.mul hc)).symm
    _ = A ^ r := by
      rw [CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]
      apply cfc_congr
      intro x hx
      change Real.exp (r * Real.log x) = x ^ r
      rw [Real.rpow_def_of_pos (hA.isStrictlyPositive.spectrum_pos hx), mul_comm]
private theorem expSandwich_power_identity {A B : Matrix d d ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (Z : Matrix d d ℂ)
    (u₀ u₁ v₀ v₁ t : ℝ) :
    expSandwich (((u₁ - u₀ : ℝ) : ℂ) • CFC.log A)
      (((v₁ - v₀ : ℝ) : ℂ) • CFC.log B) (A ^ u₀ * Z * B ^ v₀) (t : ℂ) =
        A ^ ((1 - t) * u₀ + t * u₁) * Z * B ^ ((1 - t) * v₀ + t * v₁) := by
  unfold expSandwich
  simp only [smul_smul, ← Complex.ofReal_mul, exp_smul_log hA, exp_smul_log hB]
  rw [← mul_assoc, ← mul_assoc, ← CFC.rpow_add hA.isUnit]
  simp only [mul_assoc]
  rw [← CFC.rpow_add hB.isUnit]
  have heA : t * (u₁ - u₀) + u₀ = (1 - t) * u₀ + t * u₁ := by ring
  have heB : v₀ + t * (v₁ - v₀) = (1 - t) * v₀ + t * v₁ := by ring
  rw [heA, heB]
end PowerInterpolationParts
section SpectralInterpolationParts
open Finset BigOperators
private def perspectiveWeight (z₀ z₁ t : ℝ) : ℝ := t * z₁ / ((1 - t) * z₀ + t * z₁)
private theorem trace_interpolation_of_weak_log_majorization {n : ℕ}
    {x y w : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hw : ∀ i, 0 ≤ w i) (hxa : Antitone x) (hya : Antitone y) (hwa : Antitone w)
    {z₀ z₁ t : ℝ} (hz₀ : 0 < z₀) (hz₁ : 0 < z₁) (ht₀ : 0 < t) (ht₁ : t < 1)
    (hmaj : ∀ (k : ℕ) (_ : k ≤ n),
      ∏ i : Fin k, w ⟨i.val, by omega⟩ ≤
        ∏ i : Fin k,
          (x ⟨i.val, by omega⟩ ^ (1 - perspectiveWeight z₀ z₁ t) *
            y ⟨i.val, by omega⟩ ^ perspectiveWeight z₀ z₁ t)) :
    ∑ i, w i ^ (2 * ((1 - t) * z₀ + t * z₁)) ≤
      (∑ i, x i ^ (2 * z₀)) ^ (1 - t) * (∑ i, y i ^ (2 * z₁)) ^ t := by
  let z := (1 - t) * z₀ + t * z₁
  let θ := perspectiveWeight z₀ z₁ t
  have hz : 0 < z := add_pos (mul_pos (by linarith) hz₀) (mul_pos ht₀ hz₁)
  have hθ : 0 < θ := div_pos (mul_pos ht₀ hz₁) hz
  have hθ' : 0 < 1 - θ := by
    dsimp [θ, perspectiveWeight]
    exact sub_pos.mpr ((div_lt_one hz).mpr (by dsimp [z] at *; nlinarith))
  have he₀ : (1 - θ) * (2 * z) = (2 * z₀) * (1 - t) := by
    dsimp [θ, perspectiveWeight, z]
    field_simp
    <;> ring
  have he₁ : θ * (2 * z) = (2 * z₁) * t := by
    dsimp [θ, perspectiveWeight, z]
    field_simp
    <;> ring
  have hbound := weak_log_maj_sum_rpow_le hw
    (fun i => mul_nonneg (Real.rpow_nonneg (hx i) _) (Real.rpow_nonneg (hy i) _))
    hwa (fun i j hij => mul_le_mul
      (Real.rpow_le_rpow (hx j) (hxa hij) hθ'.le)
      (Real.rpow_le_rpow (hy j) (hya hij) hθ.le)
      (Real.rpow_nonneg (hy j) _) (Real.rpow_nonneg (hx i) _))
    hmaj (show 0 < 2 * z by positivity)
  have hid (i : Fin n) : (x i ^ (1 - θ) * y i ^ θ) ^ (2 * z) =
      (x i ^ (2 * z₀)) ^ (1 - t) * (y i ^ (2 * z₁)) ^ t := by
    rw [Real.mul_rpow (Real.rpow_nonneg (hx i) _) (Real.rpow_nonneg (hy i) _),
      ← Real.rpow_mul (hx i), ← Real.rpow_mul (hy i), he₀, he₁,
      Real.rpow_mul (hx i), Real.rpow_mul (hy i)]
  have hholder := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
    (f := fun i => (x i ^ (2 * z₀)) ^ (1 - t))
    (g := fun i => (y i ^ (2 * z₁)) ^ t)
    (Real.HolderConjugate.inv_inv (by linarith : 0 < 1 - t) ht₀ (by ring))
    (fun i _ => Real.rpow_nonneg (Real.rpow_nonneg (hx i) _) _)
    (fun i _ => Real.rpow_nonneg (Real.rpow_nonneg (hy i) _) _)
  have hp₀ (i : Fin n) : ((x i ^ (2 * z₀)) ^ (1 - t)) ^ (1 - t)⁻¹ =
      x i ^ (2 * z₀) := by
    rw [← Real.rpow_mul (Real.rpow_nonneg (hx i) _),
      mul_inv_cancel₀ (by linarith : 1 - t ≠ 0), Real.rpow_one]
  have hp₁ (i : Fin n) : ((y i ^ (2 * z₁)) ^ t) ^ t⁻¹ = y i ^ (2 * z₁) := by
    rw [← Real.rpow_mul (Real.rpow_nonneg (hy i) _),
      mul_inv_cancel₀ ht₀.ne', Real.rpow_one]
  simp only [hp₀, hp₁, one_div, inv_inv] at hholder
  exact hbound.trans ((Finset.sum_congr rfl (fun i _ => hid i)).trans_le hholder)
end SpectralInterpolationParts
section TraceSpectralParts
open _root_.Matrix BigOperators
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {d : Type*} [Fintype d] [DecidableEq d]
private theorem traceMoment_eq_sum (X : Matrix d d ℂ) (z : ℝ) :
    traceMoment X z = ∑ i, singularValues X i ^ (2 * z) := by
  unfold traceMoment
  have hg : Xᴴ * X = Xᴴ * Xᴴᴴ := by rw [conjTranspose_conjTranspose]
  rw [hg, CFC.rpow_eq_cfc_real (Matrix.posSemidef_self_mul_conjTranspose Xᴴ).nonneg,
    (isHermitian_mul_conjTranspose_self Xᴴ).cfc_eq]
  have ht := schattenNorm_trace_as_eigenvalue_sum X (2 * z)
  have he : 2 * z / 2 = z := by ring
  simp only [he, RCLike.re_to_complex] at ht
  trans ∑ i, (isHermitian_mul_conjTranspose_self Xᴴ).eigenvalues i ^ z
  · exact ht
  apply Finset.sum_congr rfl
  intro i _
  rw [singularValues, Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul (eigenvalues_self_mul_conjTranspose_nonneg Xᴴ i)]
  congr 1
  ring
private theorem traceMoment_eq_sum_sorted (X : Matrix d d ℂ) (z : ℝ) :
    traceMoment X z = ∑ i, singularValuesSorted X i ^ (2 * z) := by
  rw [traceMoment_eq_sum, sum_singularValues_rpow_eq_sum_sorted]
end TraceSpectralParts
section TraceConvexityParts
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.Matrix BigOperators Set
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩
private theorem power_weak_log_majorization {A B : Matrix d d ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (u₀ u₁ v₀ v₁ : ℝ)
    (k : ℕ) (hk : k ≤ Fintype.card d) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∏ i : Fin k, singularValuesSorted
      (A ^ ((1 - t) * u₀ + t * u₁) * B ^ ((1 - t) * v₀ + t * v₁)) ⟨i.val, by omega⟩) ≤
      ∏ i : Fin k, (singularValuesSorted (A ^ u₀ * B ^ v₀) ⟨i.val, by omega⟩ ^ (1 - t) *
        singularValuesSorted (A ^ u₁ * B ^ v₁) ⟨i.val, by omega⟩ ^ t) := by
  have hh := expSandwich_weak_log_majorization
    (H := ((u₁ - u₀ : ℝ) : ℂ) • CFC.log A)
    (K := ((v₁ - v₀ : ℝ) : ℂ) • CFC.log B)
    (by simpa only [Complex.coe_smul] using
      (IsSelfAdjoint.all (u₁ - u₀)).smul (IsSelfAdjoint.log (a := A)))
    (by simpa only [Complex.coe_smul] using
      (IsSelfAdjoint.all (v₁ - v₀)).smul (IsSelfAdjoint.log (a := B)))
    (A ^ u₀ * 1 * B ^ v₀) k hk ht
  rw [expSandwich_power_identity hA hB, ← Complex.ofReal_one,
    expSandwich_power_identity hA hB] at hh
  simp only [sub_self, zero_mul, one_mul, zero_add, mul_one] at hh
  rw [Finset.prod_mul_distrib,
    Real.finsetProd_rpow _ _ (fun _ _ => singularValuesSorted_nonneg _ _) _,
    Real.finsetProd_rpow _ _ (fun _ _ => singularValuesSorted_nonneg _ _) _]
  exact hh
private theorem renyiQ_interpolation {ρ σ : Matrix d d ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (a₀ a₁ : ℝ) {z₀ z₁ : ℝ} (hz₀ : 0 < z₀) (hz₁ : 0 < z₁)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    renyiQ ρ σ ((1 - t) * a₀ + t * a₁) ((1 - t) * z₀ + t * z₁) ≤
      renyiQ ρ σ a₀ z₀ ^ (1 - t) * renyiQ ρ σ a₁ z₁ ^ t := by
  rcases eq_or_lt_of_le ht₀ with ht | ht
  · subst t
    simp
  rcases eq_or_lt_of_le ht₁ with ht' | ht'
  · subst t
    simp
  let z := (1 - t) * z₀ + t * z₁
  let θ := perspectiveWeight z₀ z₁ t
  have hz : 0 < z := add_pos (mul_pos (by linarith) hz₀) (mul_pos ht hz₁)
  have hθ : θ ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact (div_pos (mul_pos ht hz₁) hz).le
    · exact (div_le_one hz).mpr (by dsimp [z]; nlinarith)
  have hu : (1 - θ) * (a₀ / (2 * z₀)) + θ * (a₁ / (2 * z₁)) =
      ((1 - t) * a₀ + t * a₁) / (2 * z) := by
    dsimp [θ, perspectiveWeight]
    field_simp
    <;> dsimp [z] at * <;> ring
  have hv : (1 - θ) * ((1 - a₀) / (2 * z₀)) + θ * ((1 - a₁) / (2 * z₁)) =
      (1 - ((1 - t) * a₀ + t * a₁)) / (2 * z) := by
    dsimp [θ, perspectiveWeight]
    field_simp
    <;> dsimp [z] at * <;> ring
  have hm (k : ℕ) (hk : k ≤ Fintype.card d) := power_weak_log_majorization hρ hσ
    (a₀ / (2 * z₀)) (a₁ / (2 * z₁)) ((1 - a₀) / (2 * z₀)) ((1 - a₁) / (2 * z₁))
    k hk hθ
  simp only [hu, hv] at hm
  unfold renyiQ
  rw [traceMoment_eq_sum_sorted, traceMoment_eq_sum_sorted, traceMoment_eq_sum_sorted]
  exact trace_interpolation_of_weak_log_majorization
    (singularValuesSorted_nonneg _) (singularValuesSorted_nonneg _)
    (singularValuesSorted_nonneg _) (singularValuesSorted_antitone _)
    (singularValuesSorted_antitone _) (singularValuesSorted_antitone _)
    hz₀ hz₁ ht ht' hm
private theorem log_convex_trace [Nonempty d] {ρ σ : Matrix d d ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    ConvexOn ℝ {p : ℝ × ℝ | 0 < p.2}
      (fun p => Real.log (renyiQ ρ σ p.1 p.2)) := by
  constructor
  · intro x hx y hy a b ha hb hab
    change 0 < a * x.2 + b * y.2
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have : b = 1 := by linarith
      simpa [this] using hy
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx) (mul_nonneg hb hy.le)
  · intro x hx y hy a b ha hb hab
    have hb1 : b ≤ 1 := by linarith
    have hab' : 1 - b = a := by linarith
    have hq := renyiQ_interpolation hρ hσ x.1 y.1 hx hy hb hb1
    rw [hab'] at hq
    have hl := Real.log_le_log (renyiQ_pos hρ hσ _ _ ) hq
    rw [Real.log_mul (Real.rpow_pos_of_pos (renyiQ_pos hρ hσ _ _) _).ne'
      (Real.rpow_pos_of_pos (renyiQ_pos hρ hσ _ _) _).ne',
      Real.log_rpow (renyiQ_pos hρ hσ x.1 x.2),
      Real.log_rpow (renyiQ_pos hρ hσ y.1 y.2)] at hl
    simpa only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using hl
end TraceConvexityParts
section SecantsParts
private theorem normalized_secants_monotone {q : ℝ → ℝ}
    (hq : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < q x)
    (hc : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x => Real.log (q x))) :
    MonotoneOn (fun x => Real.log (q x / q 1) / (x - 1))
      (Set.Ioi (0 : ℝ) \ {1}) := by
  intro x hx y hy hxy
  change Real.log (q x / q 1) / (x - 1) ≤ Real.log (q y / q 1) / (y - 1)
  rw [Real.log_div (hq x hx.1).ne' (hq 1 (by norm_num)).ne',
    Real.log_div (hq y hy.1).ne' (hq 1 (by norm_num)).ne']
  exact hc.secant_mono (by norm_num) hx.1 hy.1
    (Set.notMem_singleton_iff.mp hx.2) (Set.notMem_singleton_iff.mp hy.2) hxy
end SecantsParts
section AtOneParts
open _root_.Matrix NormedSpace
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance atOnePow : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩
local instance atOneRatAlgebra : NormedAlgebra ℚ (Matrix d d ℂ) := .restrictScalars ℚ ℂ _
private theorem hasDerivAt_matrix_rpow {A : Matrix d d ℂ} (hA : A.PosDef) (a : ℝ) :
    HasDerivAt (fun x : ℝ => A ^ x) (A ^ a * CFC.log A) a := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (CFC.log A) a
  simpa only [← Complex.coe_smul, exp_smul_log hA] using h
private theorem renyiQ_petz {ρ σ : Matrix d d ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (a : ℝ) :
    renyiQ ρ σ a 1 = (Matrix.trace (ρ ^ a * σ ^ (1-a))).re := by
  have hr (x : ℝ) : (ρ ^ x : Matrix d d ℂ)ᴴ = ρ ^ x :=
    (hρ.isStrictlyPositive.rpow ρ x).isSelfAdjoint.star_eq
  have hs (x : ℝ) : (σ ^ x : Matrix d d ℂ)ᴴ = σ ^ x :=
    (hσ.isStrictlyPositive.rpow σ x).isSelfAdjoint.star_eq
  unfold renyiQ traceMoment renyiProduct
  rw [CFC.rpow_one _ (Matrix.posSemidef_conjTranspose_mul_self _).nonneg]
  simp only [mul_one, Matrix.conjTranspose_mul, hr, hs]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc (σ ^ _) (ρ ^ _),
    ← CFC.rpow_add hρ.isUnit]
  have he : a / 2 + a / 2 = a := by ring
  rw [he, Matrix.trace_mul_cycle, ← CFC.rpow_add hσ.isUnit]
  have hs' : (1-a)/2 + (1-a)/2 = 1-a := by ring
  rw [hs', Matrix.trace_mul_comm]
def umegaki (ρ σ : Matrix d d ℂ) : ℝ :=
  (Matrix.trace (ρ * (CFC.log ρ - CFC.log σ))).re / (Matrix.trace ρ).re
private theorem petz_log_trace_hasDerivAt_one [Nonempty d] {ρ σ : Matrix d d ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    HasDerivAt (fun a => Real.log (renyiQ ρ σ a 1)) (umegaki ρ σ) 1 := by
  have hr := hasDerivAt_matrix_rpow hρ (1 : ℝ)
  have hs := (hasDerivAt_matrix_rpow hσ (1 - (1 : ℝ))).scomp (1 : ℝ)
    ((hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (1 : ℝ)))
  have hd := hr.mul hs
  let T : Matrix d d ℂ →L[ℝ] ℝ := Complex.reCLM.comp
    (Matrix.traceLinearMap d ℝ ℂ).toContinuousLinearMap
  have ht := T.hasFDerivAt.comp_hasDerivAt 1 hd
  have he : HasDerivAt (fun a => renyiQ ρ σ a 1)
      (Matrix.trace (ρ * (CFC.log ρ - CFC.log σ))).re 1 := by
    change HasDerivAt (fun a : ℝ => (Matrix.trace (ρ ^ a * σ ^ (1-a))).re)
      (Matrix.trace (ρ ^ (1 : ℝ) * CFC.log ρ * σ ^ (1-(1 : ℝ)) +
        ρ ^ (1 : ℝ) * ((0-1 : ℝ) • (σ ^ (1-(1 : ℝ)) * CFC.log σ)))).re 1 at ht
    simpa only [renyiQ_petz hρ hσ, Function.comp_apply, sub_self,
      CFC.rpow_one ρ hρ.posSemidef.nonneg, CFC.rpow_zero σ hσ.posSemidef.nonneg,
      one_mul, mul_one, zero_sub, neg_smul, one_smul,
      mul_neg, ← Matrix.mul_sub, smul_eq_mul, mul_neg_one,
      ← sub_eq_add_neg, T, ContinuousLinearMap.comp_apply,
      LinearMap.coe_toContinuousLinearMap', Matrix.traceLinearMap] using ht
  convert he.log (renyiQ_pos hρ hσ 1 1).ne' using 1
  simp only [renyiQ_one hρ hσ one_ne_zero, umegaki]
end AtOneParts
section ResultParts
open _root_.Matrix Set
open scoped MatrixOrder ComplexOrder
variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
private lemma affineZ_pos {κ z₀ α : ℝ} (hκ : 0 < κ) (hz₀ : 0 ≤ z₀) (hα : 0 < α) :
    0 < affineZ κ z₀ α := add_pos_of_pos_of_nonneg (mul_pos hκ hα) hz₀
private theorem affine_log_trace_convex {ρ σ : Matrix d d ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {κ z₀ : ℝ} (hκ : 0 < κ) (hz₀ : 0 ≤ z₀) :
    ConvexOn ℝ (Ioi (0 : ℝ))
      (fun α => Real.log (renyiQ ρ σ α (affineZ κ z₀ α))) := by
  refine ⟨convex_Ioi _, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := (log_convex_trace hρ hσ).2
    (x := (x, affineZ κ z₀ x)) (y := (y, affineZ κ z₀ y))
    (affineZ_pos hκ hz₀ hx) (affineZ_pos hκ hz₀ hy) ha hb hab
  have he : affineZ κ z₀ (a * x + b * y) =
      a * affineZ κ z₀ x + b * affineZ κ z₀ y := by
    unfold affineZ
    nlinarith [hab]
  simpa only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, he] using h
private theorem affine_renyi_monotone {ρ σ : Matrix d d ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {κ z₀ : ℝ} (hκ : 0 < κ) (hz₀ : 0 ≤ z₀) :
    MonotoneOn (fun α => renyiD ρ σ α (affineZ κ z₀ α)) (Ioi (0 : ℝ) \ {1}) := by
  have h := normalized_secants_monotone
    (q := fun α => renyiQ ρ σ α (affineZ κ z₀ α))
    (fun α _ => renyiQ_pos hρ hσ α _) (affine_log_trace_convex hρ hσ hκ hz₀)
  rw [renyiQ_one hρ hσ (affineZ_pos hκ hz₀ zero_lt_one).ne'] at h
  exact h
end ResultParts
section ScalarDerivativeParts
open Set Filter
open scoped Topology
private theorem flat_vertical_affine_hasDerivAt {f : ℝ × ℝ → ℝ} {c m κ z₀ : ℝ}
    (hc : ConvexOn ℝ {p : ℝ × ℝ | 0 < p.2} f)
    (hflat : ∀ z, 0 < z → f (1,z) = c)
    (hd : HasDerivAt (fun a => f (a,1)) m 1)
    (hsupport : ∀ a z, 0 < z → m*(a-1) ≤ f (a,z)-c)
    (hz : 0 < κ+z₀) :
    HasDerivAt (fun a => f (a,κ*a+z₀)) m 1 := by
  let t : ℝ := min ((κ+z₀)/2) (1/2)
  have ht : 0 < t := lt_min (by linarith) (by norm_num)
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have htz : t < κ+z₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hev : ∀ᶠ a : ℝ in 𝓝 1, t < κ*a+z₀ := by
    have hcont : ContinuousAt (fun a : ℝ => κ*a+z₀) 1 := by fun_prop
    exact hcont.eventually (eventually_gt_nhds (by simpa using htz))
  let g : ℝ → ℝ := fun a => t*f (1+(a-1)/t,1)+(1-t)*c
  have hg : HasDerivAt g m 1 := by
    have hi : HasDerivAt (fun a : ℝ => 1+(a-1)/t) (1/t) 1 := by
      convert (((hasDerivAt_id 1).sub_const 1).div_const t).const_add 1 using 1 <;> simp
    have hd' : HasDerivAt (fun a => f (a,1)) m (1+((1 : ℝ)-1)/t) := by
      simpa using hd
    have hh := ((hd'.comp 1 hi).const_mul t).add_const ((1-t)*c)
    convert hh using 1 <;> simp [g] <;> field_simp [ht.ne'] <;> ring
  have hg1 : g 1 = c := by simp [g, hflat 1 zero_lt_one]; ring
  have hf1 : f (1,κ*1+z₀) = c := hflat _ (by simpa using hz)
  have hupper : ∀ᶠ a : ℝ in 𝓝 1, f (a,κ*a+z₀) ≤ g a := by
    filter_upwards [hev] with a ha
    have hy : 0 < (κ*a+z₀-t)/(1-t) :=
      div_pos (by linarith) (by linarith)
    have hh := hc.2 (x := (1+(a-1)/t,(1 : ℝ)))
      (y := (1,(κ*a+z₀-t)/(1-t))) (by change (0 : ℝ) < 1; norm_num) hy ht.le
      (by linarith : 0 ≤ 1-t) (by ring : t+(1-t)=1)
    have he : t • (1+(a-1)/t,1) +
        (1-t) • (1,(κ*a+z₀-t)/(1-t)) = (a,κ*a+z₀) := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul]
      · field_simp [ht.ne']; ring
      · field_simp [sub_ne_zero.mpr ht1.ne']; ring
    rw [he, hflat _ hy] at hh
    simpa only [smul_eq_mul, g] using hh
  apply HasDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [hg.isLittleO.bound hε, hev, hupper] with a hbound ha hu
  have hlo : 0 ≤ f (a,κ*a+z₀)-c-(a-1)*m := by
    have hh := hsupport a (κ*a+z₀) (lt_trans ht ha)
    nlinarith
  have hle : f (a,κ*a+z₀)-c-(a-1)*m ≤ g a-c-(a-1)*m := by linarith
  simp only [Real.norm_eq_abs, smul_eq_mul, hg1] at hbound
  simp only [Real.norm_eq_abs, smul_eq_mul, hf1]
  rw [abs_of_nonneg hlo]
  exact hle.trans ((le_abs_self _).trans hbound)
end ScalarDerivativeParts
section ExtendedResultParts
open Set Filter
open scoped Topology MatrixOrder ComplexOrder
private theorem flat_vertical_support {f : ℝ × ℝ → ℝ} {c m : ℝ}
    (hc : ConvexOn ℝ {p : ℝ × ℝ | 0 < p.2} f)
    (hflat : ∀ z, 0 < z → f (1,z) = c)
    (hd : HasDerivAt (fun a => f (a,1)) m 1)
    (a z : ℝ) (hz : 0 < z) : m * (a-1) ≤ f (a,z) - c := by
  have hg : HasDerivAt (fun t : ℝ => f (1+t*(a-1),1)) (m*(a-1)) 0 := by
    have hd' : HasDerivAt (fun a => f (a,1)) m (1+0*(a-1)) := by simpa using hd
    convert hd'.comp 0 ((hasDerivAt_const 0 (1 : ℝ)).add
      ((hasDerivAt_id 0).mul_const (a-1))) using 1 <;> simp [Function.comp_def]
  apply le_of_tendsto hg.tendsto_slope_zero_right
  have ht1 : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have htz : ∀ᶠ t : ℝ in 𝓝[>] 0, t*z < 1 := by
    have hlim : Tendsto (fun t : ℝ => t*z) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
      simpa using (tendsto_nhdsWithin_of_tendsto_nhds (f := fun t : ℝ => t*z)
        (by fun_prop : ContinuousAt (fun t : ℝ => t*z) 0))
    exact hlim.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [ht1, htz, self_mem_nhdsWithin] with t ht1 htz ht
  have htp : 0 < t := ht
  have hv : 0 < (1-t*z)/(1-t) := div_pos (by linarith) (by linarith)
  have h := hc.2 (x := (a,z)) (y := (1,(1-t*z)/(1-t))) hz hv
    (le_of_lt htp) (by linarith : 0 ≤ 1-t) (by ring : t+(1-t)=1)
  have he : t • (a,z) + (1-t) • (1,(1-t*z)/(1-t)) = (1+t*(a-1),1) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    · ring
    · field_simp
      <;> ring
  rw [he, hflat _ hv] at h
  simp only [smul_eq_mul] at h
  simp only [zero_add, zero_mul, add_zero, hflat 1 zero_lt_one, smul_eq_mul] at ⊢
  rw [← div_eq_inv_mul, div_le_iff₀ htp]
  nlinarith [h]
def hiaiD {d : Type*} [Fintype d] [DecidableEq d]
    (ρ σ : Matrix d d ℂ) (a z : ℝ) : ℝ :=
  if a = 1 then umegaki ρ σ else renyiD ρ σ a z
private theorem renyi_support_bound {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    {ρ σ : Matrix d d ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (a z : ℝ) (hz : 0 < z) :
    umegaki ρ σ * (a-1) ≤ Real.log (renyiQ ρ σ a z) - Real.log (Matrix.trace ρ).re := by
  apply flat_vertical_support (log_convex_trace hρ hσ) _
    (petz_log_trace_hasDerivAt_one hρ hσ) a z hz
  intro z hz
  rw [renyiQ_one hρ hσ hz.ne']
private theorem affine_log_trace_hasDerivAt_one {d : Type*} [Fintype d] [DecidableEq d]
    [Nonempty d] {ρ σ : Matrix d d ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {κ z₀ : ℝ} (hz : 0 < κ+z₀) :
    HasDerivAt (fun a => Real.log (renyiQ ρ σ a (affineZ κ z₀ a)))
      (umegaki ρ σ) 1 := by
  apply flat_vertical_affine_hasDerivAt (log_convex_trace hρ hσ) _
    (petz_log_trace_hasDerivAt_one hρ hσ) (renyi_support_bound hρ hσ) hz
  intro z hz
  rw [renyiQ_one hρ hσ hz.ne']
private theorem positive_definite_monotone {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    {ρ σ : Matrix d d ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    {κ z₀ : ℝ} (hκ : 0 < κ) (hz₀ : 0 ≤ z₀) :
    MonotoneOn (fun a => hiaiD ρ σ a (affineZ κ z₀ a)) (Ioi (0 : ℝ)) := by
  have hc := affine_log_trace_convex hρ hσ hκ hz₀
  have hd := affine_log_trace_hasDerivAt_one hρ hσ (add_pos_of_pos_of_nonneg hκ hz₀)
  intro a ha b hb hab
  by_cases ha1 : a = 1
  · subst a
    by_cases hb1 : b = 1
    · subst b; rfl
    · have h := hc.le_slope_of_hasDerivAt (by norm_num : (1 : ℝ) ∈ Ioi 0) hb
        (by grind : (1 : ℝ) < b) hd
      simp only [hiaiD, if_neg hb1, ite_true, renyiD]
      rw [Real.log_div (renyiQ_pos hρ hσ _ _).ne' hρ.trace_pos.1.ne']
      simpa only [slope_def_field, renyiQ_one hρ hσ
        (affineZ_pos hκ hz₀ zero_lt_one).ne'] using h
  · by_cases hb1 : b = 1
    · subst b
      have h := hc.slope_le_of_hasDerivAt ha (by norm_num : (1 : ℝ) ∈ Ioi 0)
        (by grind : a < (1 : ℝ)) hd
      simp only [hiaiD, if_neg ha1, ite_true, renyiD]
      rw [Real.log_div (renyiQ_pos hρ hσ _ _).ne' hρ.trace_pos.1.ne']
      rw [slope_comm] at h
      simpa only [slope_def_field, renyiQ_one hρ hσ
        (affineZ_pos hκ hz₀ zero_lt_one).ne'] using h
    · simp only [hiaiD, if_neg ha1, if_neg hb1]
      exact affine_renyi_monotone hρ hσ hκ hz₀ ⟨ha,ha1⟩ ⟨hb,hb1⟩ hab
end ExtendedResultParts
section SemidefiniteParts
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open _root_.Matrix Filter Topology
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Hiai.SupportPowerLimits
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance semidefinitePow : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩
private lemma shift_tendsto (A : Matrix d d ℂ) :
    Tendsto (fun ε : ℝ => A + ε • (1 : Matrix d d ℂ))
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 A) := by
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  simpa using tendsto_const_nhds.add (he.smul_const (1 : Matrix d d ℂ))
private lemma positive_shift {A : Matrix d d ℂ} (hA : A.PosSemidef) :
    ∀ᶠ ε : ℝ in (𝓝[Set.Ioi (0 : ℝ)] 0),
      (A + ε • (1 : Matrix d d ℂ)).PosSemidef := by
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hA.add (Matrix.PosSemidef.one.smul (le_of_lt hε))
private theorem renyiProduct_regularization_tendsto {ρ σ : Matrix d d ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hs : ∀ x : d → ℂ, σ *ᵥ x = 0 → ρ *ᵥ x = 0)
    {α z : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) (hz : 0 < z) :
    Tendsto (fun ε : ℝ => renyiProduct (ρ + ε • 1) (σ + ε • 1) α z)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (renyiProduct ρ σ α z)) := by
  let u := α / (2 * z)
  let v := (1 - α) / (2 * z)
  let Q := 1 - spectralSupport σ
  let R (ε : ℝ) := cfc (fun x : ℝ => if x = 0 then 0 else (x + ε) ^ v) σ
  have hu : 0 < u := div_pos hα (by positivity)
  have hv : v ≠ 0 := div_ne_zero (sub_ne_zero.mpr (Ne.symm hα1)) (by positivity)
  have huv : 0 < u + v := by
    dsimp [u, v]
    rw [← add_div]
    ring_nf
    positivity
  obtain ⟨hqs, hqq, hqpos, hσq, hρq⟩ := kernel_projection_data hσ hs
  have hR : Tendsto R (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (σ ^ v)) :=
    support_rpow_shift_tendsto hσ hv
  have hU := tendsto_positive_rpow hu hρ (positive_shift hρ) (shift_tendsto ρ)
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hcorr : Tendsto (fun ε : ℝ => ε ^ (u + v) • Q)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (0 : Matrix d d ℂ)) := by
    have hpow := (Real.continuous_rpow_const huv.le).continuousAt.tendsto.comp he
    simpa [Real.zero_rpow huv.ne'] using hpow.smul_const Q
  have hlim := (hU.mul hR).add hcorr
  have heq : ∀ᶠ ε : ℝ in (𝓝[Set.Ioi (0 : ℝ)] 0),
      renyiProduct (ρ + ε • 1) (σ + ε • 1) α z =
        (ρ + ε • 1) ^ u * R ε + ε ^ (u + v) • Q := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hρe : (ρ + ε • (1 : Matrix d d ℂ)).PosSemidef :=
      hρ.add (Matrix.PosSemidef.one.smul hε.le)
    have hUQ : (ρ + ε • (1 : Matrix d d ℂ)) ^ u * Q = ε ^ u • Q := by
      apply rpow_on_eigenmatrix hρe
      simp [Q, Matrix.add_mul, Matrix.smul_mul, hρq]
    unfold renyiProduct
    change (ρ + ε • 1) ^ u * (σ + ε • 1) ^ v = _
    rw [inverse_shift_split hσ hε v]
    change (ρ + ε • 1) ^ u * (R ε + ε ^ v • Q) = _
    rw [Matrix.mul_add, Matrix.mul_smul, hUQ, smul_smul]
    rw [← Real.rpow_add hε, add_comm v u]
  simpa [renyiProduct, u, v] using
    (hlim.congr' (heq.mono fun _ h => h.symm))
private theorem renyiQ_regularization_tendsto {ρ σ : Matrix d d ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hs : ∀ x : d → ℂ, σ *ᵥ x = 0 → ρ *ᵥ x = 0)
    {α z : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) (hz : 0 < z) :
    Tendsto (fun ε : ℝ => renyiQ (ρ + ε • 1) (σ + ε • 1) α z)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (renyiQ ρ σ α z)) := by
  let P (ε : ℝ) := renyiProduct (ρ + ε • 1) (σ + ε • 1) α z
  let P₀ := renyiProduct ρ σ α z
  have hP := renyiProduct_regularization_tendsto hρ hσ hs hα hα1 hz
  have hG : Tendsto (fun ε : ℝ => (P ε)ᴴ * P ε)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (P₀ᴴ * P₀)) := by
    exact ((continuous_id.matrix_conjTranspose.continuousAt.tendsto).comp hP).mul hP
  simpa only [renyiQ, traceMoment,
    D5.S3.Quantum.Hiai.InverseMeanVariational.tracePower, P, P₀] using
    tendsto_tracePower hz (Matrix.posSemidef_conjTranspose_mul_self P₀)
      (Filter.Eventually.of_forall fun ε => Matrix.posSemidef_conjTranspose_mul_self (P ε)) hG
private lemma psd_trace_pos {A : Matrix d d ℂ} (hA : A.PosSemidef) (hA0 : A ≠ 0) :
    0 < (Matrix.trace A).re := by
  have hn := (Complex.nonneg_iff.mp hA.trace_nonneg).1
  apply lt_of_le_of_ne hn
  intro he
  have hi := (Complex.nonneg_iff.mp hA.trace_nonneg).2
  exact hA0 (hA.trace_eq_zero_iff.mp (Complex.ext he.symm hi.symm))
private lemma psd_rpow_ne_zero {A : Matrix d d ℂ} (hA : A.PosSemidef)
    (hA0 : A ≠ 0) {q : ℝ} (hq : q ≠ 0) : A ^ q ≠ 0 := by
  intro he
  have h := psd_nested_rpow hA q (1 / q)
  rw [he, mul_one_div_cancel hq, CFC.rpow_one A hA.nonneg] at h
  have hz : (0 : Matrix d d ℂ) ^ (1 / q) = 0 :=
    CFC.zero_rpow (one_div_ne_zero hq)
  rw [hz] at h
  exact hA0 h.symm
private lemma product_ne_zero {ρ σ : Matrix d d ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hρ0 : ρ ≠ 0)
    (hs : ∀ x : d → ℂ, σ *ᵥ x = 0 → ρ *ᵥ x = 0)
    {α z : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) (hz : 0 < z) :
    renyiProduct ρ σ α z ≠ 0 := by
  let u := α / (2 * z)
  let v := (1 - α) / (2 * z)
  have hu : u ≠ 0 := ne_of_gt (div_pos hα (by positivity))
  have hv : v ≠ 0 := div_ne_zero (sub_ne_zero.mpr (Ne.symm hα1)) (by positivity)
  obtain ⟨_, _, _, _, hρq⟩ := kernel_projection_data hσ hs
  have hρuq : ρ ^ u * (1 - spectralSupport σ) = 0 := by
    simpa [Real.zero_rpow hu] using rpow_on_eigenmatrix hρ 0 u (by simpa using hρq)
  have hright : σ ^ v * σ ^ (-v) = spectralSupport σ := by
    rw [CFC.rpow_eq_cfc_real hσ.nonneg, CFC.rpow_eq_cfc_real hσ.nonneg]
    rw [← cfc_mul _ _ σ (σ.finite_real_spectrum.continuousOn _)
      (σ.finite_real_spectrum.continuousOn _)]
    unfold spectralSupport
    apply cfc_congr
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0, Real.zero_rpow hv]
    · change x ^ v * x ^ (-v) = if x = 0 then 0 else 1
      rw [← Real.rpow_add (lt_of_le_of_ne (by
          rw [hσ.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
          obtain ⟨i, rfl⟩ := hx
          exact hσ.eigenvalues_nonneg i) (Ne.symm hx0))]
      simp [hx0]
  intro he
  have hmul := congrArg (fun M : Matrix d d ℂ => M * σ ^ (-v)) he
  change ρ ^ u * σ ^ v * σ ^ (-v) = 0 * σ ^ (-v) at hmul
  rw [Matrix.mul_assoc, hright, Matrix.zero_mul] at hmul
  have hρu : ρ ^ u = 0 := by
    simpa [Matrix.mul_sub, hmul] using hρuq
  exact psd_rpow_ne_zero hρ hρ0 hu hρu
private theorem renyiQ_psd_pos {ρ σ : Matrix d d ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hρ0 : ρ ≠ 0)
    (hs : ∀ x : d → ℂ, σ *ᵥ x = 0 → ρ *ᵥ x = 0)
    {α z : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) (hz : 0 < z) :
    0 < renyiQ ρ σ α z := by
  let P := renyiProduct ρ σ α z
  have hP : P ≠ 0 := product_ne_zero hρ hσ hρ0 hs hα hα1 hz
  have hG : Pᴴ * P ≠ 0 := fun h => hP (Matrix.conjTranspose_mul_self_eq_zero.mp h)
  exact psd_trace_pos (Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg)
    (psd_rpow_ne_zero (Matrix.posSemidef_conjTranspose_mul_self P) hG hz.ne')
private theorem renyiD_regularization_tendsto {ρ σ : Matrix d d ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hρ0 : ρ ≠ 0)
    (hs : ∀ x : d → ℂ, σ *ᵥ x = 0 → ρ *ᵥ x = 0)
    {α z : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) (hz : 0 < z) :
    Tendsto (fun ε : ℝ => renyiD (ρ + ε • 1) (σ + ε • 1) α z)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (renyiD ρ σ α z)) := by
  have hQ := renyiQ_regularization_tendsto hρ hσ hs hα hα1 hz
  have htrace : Continuous (fun X : Matrix d d ℂ => (Matrix.trace X).re) := by
    unfold Matrix.trace
    fun_prop
  have ht := htrace.continuousAt.tendsto.comp (shift_tendsto ρ)
  have hquot := hQ.div ht (psd_trace_pos hρ hρ0).ne'
  have hpos : 0 < renyiQ ρ σ α z / (Matrix.trace ρ).re :=
    div_pos (renyiQ_psd_pos hρ hσ hρ0 hs hα hα1 hz) (psd_trace_pos hρ hρ0)
  exact ((Real.continuousAt_log hpos.ne').tendsto.comp hquot).div_const (α - 1)
end SemidefiniteParts
section SemidefiniteLogParts
open _root_.Matrix Filter Topology
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Hiai.SupportPowerLimits
variable {d : Type*} [Fintype d] [DecidableEq d]
private lemma finite_cfc_limit {A : Matrix d d ℂ} {F : ℝ → ℝ → ℝ} {f : ℝ → ℝ}
    (hf : ∀ x ∈ spectrum ℝ A,
      Tendsto (fun ε : ℝ => F ε x) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (f x))) :
    Tendsto (fun ε : ℝ => cfc (F ε) A) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (cfc f A)) := by
  apply tendsto_cfc_fun
  · rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    apply A.finite_real_spectrum.eventually_all.mpr
    intro x hx
    simpa [dist_comm] using (Metric.tendsto_nhds.1 (hf x hx)) δ hδ
  · exact Filter.Eventually.of_forall fun _ => A.finite_real_spectrum.continuousOn _
private lemma log_shift_formula {A : Matrix d d ℂ} (hA : A.PosSemidef) (ε : ℝ) :
    CFC.log (A + ε • (1 : Matrix d d ℂ)) =
      cfc (fun x : ℝ => Real.log (x + ε)) A := by
  have haff : cfc (fun x : ℝ => x + ε) A = A + ε • (1 : Matrix d d ℂ) := by
    rw [cfc_add_const ε (fun x : ℝ => x) A
      (A.finite_real_spectrum.continuousOn _) hA.isHermitian.isSelfAdjoint,
      cfc_id' ℝ A hA.isHermitian.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]
  unfold CFC.log
  rw [← haff]
  exact (cfc_comp' Real.log (fun x : ℝ => x + ε) A
    ((A.finite_real_spectrum.image _).continuousOn _)
    (A.finite_real_spectrum.continuousOn _) hA.isHermitian.isSelfAdjoint).symm
private lemma support_log_shift_tendsto {A : Matrix d d ℂ} (hA : A.PosSemidef) :
    Tendsto (fun ε : ℝ => cfc (fun x : ℝ => if x = 0 then 0 else Real.log (x + ε)) A)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (CFC.log A)) := by
  apply finite_cfc_limit
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0, Real.log_zero]
  · simp only [if_neg hx0]
    have hid : Tendsto (fun ε : ℝ => ε) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hlim : Tendsto (fun ε : ℝ => x + ε) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (x + 0)) :=
      tendsto_const_nhds.add hid
    have hcont : ContinuousAt Real.log x := Real.continuousAt_log hx0
    exact hcont.tendsto.comp (by simpa using hlim)
private lemma log_shift_split {A : Matrix d d ℂ} (hA : A.PosSemidef) (ε : ℝ) :
    CFC.log (A + ε • (1 : Matrix d d ℂ)) =
      cfc (fun x : ℝ => if x = 0 then 0 else Real.log (x + ε)) A +
        Real.log ε • (1 - spectralSupport A) := by
  rw [log_shift_formula hA]
  have hQ : 1 - spectralSupport A = cfc (fun x : ℝ => if x = 0 then 1 else 0) A := by
    unfold spectralSupport
    rw [← cfc_const_one ℝ A hA.isHermitian.isSelfAdjoint,
      ← cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => if x = 0 then 0 else 1) A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    apply cfc_congr
    intro x hx
    by_cases h : x = 0 <;> simp [h]
  rw [hQ, ← cfc_smul (Real.log ε) _ A (A.finite_real_spectrum.continuousOn _),
    ← cfc_add A _ _ (A.finite_real_spectrum.continuousOn _)
      (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro x hx
  by_cases h : x = 0 <;> simp [h]
private lemma self_log_regularization_tendsto {A : Matrix d d ℂ} (hA : A.PosSemidef) :
    Tendsto (fun ε : ℝ => (A + ε • 1) * CFC.log (A + ε • 1))
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (A * CFC.log A)) := by
  have heq (ε : ℝ) : (A + ε • 1) * CFC.log (A + ε • 1) =
      cfc (fun x : ℝ => (x + ε) * Real.log (x + ε)) A := by
    rw [log_shift_formula hA]
    have haff : cfc (fun x : ℝ => x + ε) A = A + ε • (1 : Matrix d d ℂ) := by
      rw [cfc_add_const ε (fun x : ℝ => x) A
        (A.finite_real_spectrum.continuousOn _) hA.isHermitian.isSelfAdjoint,
        cfc_id' ℝ A hA.isHermitian.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]
    rw [← haff, ← cfc_mul _ _ A (A.finite_real_spectrum.continuousOn _)
      (A.finite_real_spectrum.continuousOn _)]
  have htarget : A * CFC.log A = cfc (fun x : ℝ => x * Real.log x) A := by
    unfold CFC.log
    conv_lhs => lhs; rw [← cfc_id' ℝ A hA.isHermitian.isSelfAdjoint]
    rw [← cfc_mul _ _ A (A.finite_real_spectrum.continuousOn _)
      (A.finite_real_spectrum.continuousOn _)]
  simp_rw [heq, htarget]
  apply finite_cfc_limit
  intro x hx
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  exact Real.continuous_mul_log.continuousAt.tendsto.comp (by simpa using
    (tendsto_const_nhds.add hid : Tendsto (fun ε : ℝ => x + ε) _ (𝓝 (x + 0))))
lemma cross_log_regularization_tendsto {ρ σ : Matrix d d ℂ}
    (hσ : σ.PosSemidef)
    (hs : ∀ x : d → ℂ, σ *ᵥ x = 0 → ρ *ᵥ x = 0) :
    Tendsto (fun ε : ℝ => (ρ + ε • 1) * CFC.log (σ + ε • 1))
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (ρ * CFC.log σ)) := by
  obtain ⟨_, _, _, _, hρq⟩ := kernel_projection_data hσ hs
  let Q := 1 - spectralSupport σ
  have heq (ε : ℝ) : (ρ + ε • 1) * CFC.log (σ + ε • 1) =
      (ρ + ε • 1) * cfc (fun x : ℝ => if x = 0 then 0 else Real.log (x + ε)) σ +
        (ε * Real.log ε) • Q := by
    rw [log_shift_split hσ]
    simp only [Matrix.mul_add, Matrix.mul_smul]
    have hq : (ρ + ε • (1 : Matrix d d ℂ)) * Q = ε • Q := by
      simp [Q, Matrix.add_mul, hρq]
    rw [hq, smul_smul, mul_comm (Real.log ε) ε]
  have hmain := (shift_tendsto ρ).mul (support_log_shift_tendsto hσ)
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hzero := (Real.continuous_mul_log.continuousAt.tendsto.comp hid).smul_const Q
  simpa [← heq] using hmain.add hzero
private theorem umegaki_regularization_tendsto {ρ σ : Matrix d d ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hρ0 : ρ ≠ 0)
    (hs : ∀ x : d → ℂ, σ *ᵥ x = 0 → ρ *ᵥ x = 0) :
    Tendsto (fun ε : ℝ => umegaki (ρ + ε • 1) (σ + ε • 1))
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (umegaki ρ σ)) := by
  have hmat := (self_log_regularization_tendsto hρ).sub
    (cross_log_regularization_tendsto hσ hs)
  have ht : Continuous (fun X : Matrix d d ℂ => (Matrix.trace X).re) := by
    unfold Matrix.trace
    fun_prop
  have hnum := ht.continuousAt.tendsto.comp hmat
  have hden := ht.continuousAt.tendsto.comp (shift_tendsto ρ)
  have hlim := hnum.div hden (psd_trace_pos hρ hρ0).ne'
  change Tendsto (fun ε : ℝ =>
    (Matrix.trace ((ρ + ε • 1) * CFC.log (ρ + ε • 1) -
      (ρ + ε • 1) * CFC.log (σ + ε • 1))).re / (Matrix.trace (ρ + ε • 1)).re)
    (𝓝[Set.Ioi (0 : ℝ)] 0)
    (𝓝 ((Matrix.trace (ρ * CFC.log ρ - ρ * CFC.log σ)).re / (Matrix.trace ρ).re)) at hlim
  simpa only [umegaki, Matrix.mul_sub] using hlim
private lemma hiaiD_regularization_tendsto {ρ σ : Matrix d d ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hρ0 : ρ ≠ 0)
    (hs : ∀ x : d → ℂ, σ *ᵥ x = 0 → ρ *ᵥ x = 0)
    {α z : ℝ} (hα : 0 < α) (hz : 0 < z) :
    Tendsto (fun ε : ℝ => hiaiD (ρ + ε • 1) (σ + ε • 1) α z)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (hiaiD ρ σ α z)) := by
  by_cases ha : α = 1
  · simpa [hiaiD, ha] using umegaki_regularization_tendsto hρ hσ hρ0 hs
  · simpa [hiaiD, ha] using renyiD_regularization_tendsto hρ hσ hρ0 hs hα ha hz
theorem result {ρ σ : Matrix d d ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hρ0 : ρ ≠ 0)
    (hs : ∀ x : d → ℂ, σ *ᵥ x = 0 → ρ *ᵥ x = 0)
    {κ z₀ : ℝ} (hκ : 0 < κ) (hz₀ : 0 ≤ z₀) :
    MonotoneOn (fun α => hiaiD ρ σ α (affineZ κ z₀ α)) (Set.Ioi (0 : ℝ)) := by
  haveI : Nonempty d := by
    by_contra hn
    haveI : IsEmpty d := not_nonempty_iff.mp hn
    exact hρ0 (Subsingleton.elim _ _)
  intro a ha b hb hab
  apply le_of_tendsto_of_tendsto
    (hiaiD_regularization_tendsto hρ hσ hρ0 hs ha (affineZ_pos hκ hz₀ ha))
    (hiaiD_regularization_tendsto hρ hσ hρ0 hs hb (affineZ_pos hκ hz₀ hb))
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hρe : (ρ + ε • (1 : Matrix d d ℂ)).PosDef :=
    Matrix.PosDef.posSemidef_add hρ (Matrix.PosDef.one.smul hε)
  have hσe : (σ + ε • (1 : Matrix d d ℂ)).PosDef :=
    Matrix.PosDef.posSemidef_add hσ (Matrix.PosDef.one.smul hε)
  exact positive_definite_monotone hρe hσe hκ hz₀ ha hb hab
end SemidefiniteLogParts
end D5.S3.Quantum.Divergence.AlphaZAffine
