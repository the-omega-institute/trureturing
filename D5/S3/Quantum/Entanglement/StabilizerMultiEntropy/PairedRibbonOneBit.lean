/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/PairedRibbonOneBit
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/PairedRibbonOneBit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp strict advantage of one joint nonlinear record on a literal paired ribbon erase mask. -/
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonMask
import OmegaBuild.Commands

compile_only_with_mathlib

noncomputable section

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonOneBit

section
open scoped BigOperators

namespace PairedOneBit

private theorem abs_fold (x : ℝ) :
    (|1+x|+|1-x|)/2 = max 1 |x| := by
  rcases le_or_gt 0 x with hp | hn
  · rw [abs_of_nonneg hp]
    rcases le_or_gt x 1 with h | h
    · rw [abs_of_nonneg (by linarith : 0 ≤ 1+x), abs_of_nonneg (by linarith : 0 ≤ 1-x),
        max_eq_left h]
      ring
    · rw [abs_of_nonneg (by linarith : 0 ≤ 1+x), abs_of_neg (by linarith : 1-x < 0),
        max_eq_right h.le]
      ring
  · rw [abs_of_neg hn]
    rcases le_or_gt (-x) 1 with h | h
    · rw [abs_of_nonneg (by linarith : 0 ≤ 1+x), abs_of_nonneg (by linarith : 0 ≤ 1-x),
        max_eq_left h]
      ring
    · rw [abs_of_neg (by linarith : 1+x < 0), abs_of_nonneg (by linarith : 0 ≤ 1-x),
        max_eq_right h.le]
      ring

private theorem sharp_pointwise (x : ℝ) : max 1 |x| ≤ 1+x^2/4 := by
  have h : |x|^2 = x^2 := sq_abs x
  apply max_le
  · nlinarith [sq_nonneg x]
  · nlinarith [sq_nonneg (|x|-2)]

private theorem flagged_one_bit_bound {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    (h : (∑ i ∈ s, (z i)^2) ≤ s.card) :
    (∑ i ∈ s, (|1+z i|+|1-z i|)/2) ≤ 5/4 * (s.card:ℝ) := by
  calc
    _ = ∑ i ∈ s, max 1 |z i| := Finset.sum_congr rfl (fun i _ => abs_fold _)
    _ ≤ ∑ i ∈ s, (1+(z i)^2/4) := Finset.sum_le_sum (fun i _ => sharp_pointwise _)
    _ = (s.card:ℝ) + (∑ i ∈ s, (z i)^2)/4 := by
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_const, nsmul_eq_mul,mul_one]
    _ ≤ _ := by linarith

end PairedOneBit
end

section
open scoped BigOperators

namespace PairedTransform
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def applyKernel (K : ι → ι → ℝ) (ε : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, K i j * ε j

private theorem exact_parseval (K : ι → ι → ℝ) (ε : ι → ℝ)
    (hK : ∀ j k : ι, ∑ i, K i j * K i k = if j=k then 1 else 0) :
    ∑ i, (applyKernel K ε i)^2 = ∑ j, (ε j)^2 := by
  classical
  calc
    _ = ∑ i, ∑ j, ∑ k, (K i j * K i k) * (ε j * ε k) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [applyKernel, pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ j, ∑ k, ∑ i, (K i j * K i k) * (ε j * ε k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ j, (ε j)^2 := by
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [← Finset.sum_mul, hK, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simp [pow_two]

private theorem binary_energy (K : ι → ι → ℝ) (ε : ι → ℝ)
    (hK : ∀ j k : ι, ∑ i, K i j * K i k = if j=k then 1 else 0)
    (he : ∀ j, |ε j| ≤ 1) :
    ∑ i, (applyKernel K ε i)^2 ≤ (Fintype.card ι : ℝ) := by
  rw [exact_parseval K ε hK]
  have h j : (ε j)^2 ≤ (1:ℝ) := by
    rw [← sq_abs]
    exact (pow_le_pow_left₀ (abs_nonneg _) (he _) 2).trans_eq (by simp)
  calc
    _ ≤ ∑ _ : ι, (1:ℝ) := Finset.sum_le_sum (fun j _ => h j)
    _ = _ := by simp

omit [DecidableEq ι] in
private theorem complementary_blocks (K : ι → ι → ℝ) (ε : ι → ℝ)
    (hK : ∀ i : ι, ∑ j, K i j = 1) (i : ι) :
    applyKernel K (fun j => (1+ε j)/2) i = (1+applyKernel K ε i)/2 ∧
    applyKernel K (fun j => (1-ε j)/2) i = (1-applyKernel K ε i)/2 := by
  constructor
  · simp only [applyKernel, ← mul_div_assoc, mul_add, mul_one]
    rw [show (∑ j, (K i j + K i j * ε j)/2) =
      (∑ j, (K i j + K i j * ε j))/2 by simp only [div_eq_mul_inv, Finset.sum_mul]]
    rw [Finset.sum_add_distrib, hK]
  · simp only [applyKernel, ← mul_div_assoc, mul_sub, mul_one]
    rw [show (∑ j, (K i j - K i j * ε j)/2) =
      (∑ j, (K i j - K i j * ε j))/2 by simp only [div_eq_mul_inv, Finset.sum_mul]]
    rw [Finset.sum_sub_distrib, hK]

end PairedTransform
end

section
open scoped BigOperators

namespace PairedTensor

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def tensor (K : ι → ι → ℝ) (L : κ → κ → ℝ) (i j : ι × κ) : ℝ :=
  K i.1 j.1 * L i.2 j.2

omit [DecidableEq ι] [DecidableEq κ] in
private theorem sum_product (f : ι → ℝ) (g : κ → ℝ) :
    (∑ i : ι × κ, f i.1 * g i.2) = (∑ i, f i) * (∑ i, g i) := by
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  simp only [Finset.mul_sum]

private theorem tensor_columns (K : ι → ι → ℝ) (L : κ → κ → ℝ)
    (hK : ∀ j k : ι, ∑ i, K i j*K i k = if j=k then 1 else 0)
    (hL : ∀ j k : κ, ∑ i, L i j*L i k = if j=k then 1 else 0)
    (x y : ι × κ) :
    ∑ z, tensor K L z x*tensor K L z y = if x=y then 1 else 0 := by
  calc
    _ = ∑ z : ι × κ, (K z.1 x.1*K z.1 y.1)*(L z.2 x.2*L z.2 y.2) := by
      apply Finset.sum_congr rfl
      intro z _
      unfold tensor
      ring
    _ = _ := by
      rw [sum_product (fun i => K i x.1*K i y.1) (fun i => L i x.2*L i y.2), hK, hL]
      simp [Prod.ext_iff]
      split <;> simp_all

omit [DecidableEq ι] [DecidableEq κ] in
private theorem tensor_mean (K : ι → ι → ℝ) (L : κ → κ → ℝ)
    (hK : ∀ i : ι, ∑ j, K i j = 1)
    (hL : ∀ i : κ, ∑ j, L i j = 1) (x : ι × κ) :
    ∑ z, tensor K L x z = 1 := by
  simp [tensor, sum_product, hK, hL]

omit [DecidableEq ι] [DecidableEq κ] in
private theorem tensor_product_encoder (K : ι → ι → ℝ) (L : κ → κ → ℝ)
    (f : ι → ℝ) (g : κ → ℝ) (x : ι × κ) :
    (∑ z, tensor K L x z * (f z.1*g z.2)) =
      (∑ i, K x.1 i*f i)*(∑ j, L x.2 j*g j) := by
  rw [← sum_product]
  apply Finset.sum_congr rfl
  intro z _
  unfold tensor
  ring

end PairedTensor
end

section
open scoped BigOperators

namespace PairedOneBit
open PairedTransform

/-- For a normalized orthogonal Bell kernel, this is the sum of the
absolute spectra of the two unnormalized classical message blocks. -/
private theorem flag_trace_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℝ) (ε : ι → ℝ)
    (hK : ∀ j k : ι, ∑ i, K i j * K i k = if j=k then 1 else 0)
    (hm : ∀ i : ι, ∑ j, K i j = 1) (he : ∀ i, |ε i| ≤ 1) :
    (∑ i : ι, (|applyKernel K (fun j => (1+ε j)/2) i| +
           |applyKernel K (fun j => (1-ε j)/2) i|)) ≤
      5/4 * (Fintype.card ι : ℝ) := by
  have h := flagged_one_bit_bound (Finset.univ : Finset ι) (applyKernel K ε)
    (by simpa using binary_energy K ε hK he)
  have heq : (∑ i : ι, (|applyKernel K (fun j => (1+ε j)/2) i| +
           |applyKernel K (fun j => (1-ε j)/2) i|)) =
      ∑ i : ι, (|1+applyKernel K ε i|+|1-applyKernel K ε i|)/2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [(complementary_blocks K ε hm i).1, (complementary_blocks K ε hm i).2]
    rw [abs_div, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), ← add_div]
  rw [heq]
  simpa using h

end PairedOneBit
end

section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace PairedSpectralTrace
variable {I : Type*} [Fintype I] [DecidableEq I]

def realDiag (f : I → ℝ) : Matrix I I ℂ :=
  diagonal fun i => (f i : ℂ)

omit [Fintype I] in
private theorem diagonal_star (f : I → ℝ) : (realDiag f)ᴴ = realDiag f := by
  simp [realDiag, diagonal_conjTranspose]

private theorem diagonal_abs_square (f : I → ℝ) :
    realDiag (fun i => |f i|)*realDiag (fun i => |f i|) = realDiag f*realDiag f := by
  unfold realDiag
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  simp only [← Complex.ofReal_mul]
  rw [← pow_two, sq_abs, pow_two]

private theorem orthogonal_spectral_trace (U : Matrix I I ℂ) (f : I → ℝ)
    (h : Uᴴ*U=1) :
    let M := U*realDiag f*Uᴴ
    ((CFC.sqrt (Mᴴ*M)).trace).re = ∑ i, |f i| := by
  let D := realDiag f
  let A := realDiag (fun i => |f i|)
  let M := U*D*Uᴴ
  let S := U*A*Uᴴ
  change ((CFC.sqrt (Mᴴ*M)).trace).re = _
  have hA : A.PosSemidef := PosSemidef.diagonal
    (fun i => Complex.nonneg_iff.mpr ⟨abs_nonneg (f i), rfl⟩)
  have hS : 0 ≤ S := nonneg_iff_posSemidef.mpr (hA.mul_mul_conjTranspose_same U)
  have hM : Mᴴ = M := by
    simp only [M, conjTranspose_mul, conjTranspose_conjTranspose, D, diagonal_star, Matrix.mul_assoc]
  have hcombine (B : Matrix I I ℂ) :
      (U*B*Uᴴ)*(U*B*Uᴴ)=U*(B*B)*Uᴴ := by
    calc
      _ = U*B*(Uᴴ*U)*B*Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by simp [h, Matrix.mul_assoc]
  have hsq : S*S=Mᴴ*M := by
    rw [hM]
    change (U*A*Uᴴ)*(U*A*Uᴴ) = (U*D*Uᴴ)*(U*D*Uᴴ)
    rw [hcombine A, hcombine D, show A*A=D*D from diagonal_abs_square f]
  rw [CFC.sqrt_unique hsq hS]
  change (trace (U*A*Uᴴ)).re = _
  rw [trace_mul_cycle, h, one_mul]
  simp [A, realDiag, trace_diagonal, ← Complex.ofReal_sum]

private theorem flagged_spectral_trace {F : Type*} [Fintype F] [DecidableEq F]
    (U : F → Matrix I I ℂ) (f : F → I → ℝ)
    (h : ∀ a, (U a)ᴴ*U a=1) :
    let M := blockDiagonal fun a => U a*realDiag (f a)*(U a)ᴴ
    ((CFC.sqrt (Mᴴ*M)).trace).re = ∑ a, ∑ i, |f a i| := by
  let V := blockDiagonal U
  have hv : Vᴴ*V = 1 := by
    unfold V
    rw [blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    simp_rw [h]
    exact blockDiagonal_one
  have hb : blockDiagonal (fun a => U a*realDiag (f a)*(U a)ᴴ) =
      V*realDiag (fun i : I × F => f i.2 i.1)*Vᴴ := by
    unfold V
    rw [blockDiagonal_conjTranspose,
      show realDiag (fun i : I × F => f i.2 i.1) =
        blockDiagonal (fun a => realDiag (f a)) from
        by unfold realDiag; exact (blockDiagonal_diagonal (fun a i => (f a i : ℂ))).symm]
    rw [← blockDiagonal_mul, ← blockDiagonal_mul]
  dsimp only
  rw [hb]
  rw [orthogonal_spectral_trace V _ hv, Fintype.sum_prod_type, Finset.sum_comm]

end PairedSpectralTrace
end

section
open Matrix
open PairedTransform PairedSpectralTrace
open scoped BigOperators ComplexOrder MatrixOrder

namespace PairedOneBit
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

def branchSpectrum (K : I → I → ℝ) (ε : I → ℝ) (b : Bool) (i : I) : ℝ :=
  (Fintype.card I : ℝ)⁻¹ *
    applyKernel K (fun j => (if b then 1+ε j else 1-ε j)/2) i

/-- Upper bound on the genuine complex square-root trace of both flag blocks,
with their original branch probabilities and a Bell spectral provider. -/
private theorem physical_flag_bound (U : Bool → Matrix I I ℂ)
    (K : I → I → ℝ) (ε : I → ℝ)
    (hU : ∀ b, (U b)ᴴ*U b=1)
    (hK : ∀ j k : I, ∑ i, K i j*K i k = if j=k then 1 else 0)
    (hm : ∀ i : I, ∑ j, K i j = 1) (he : ∀ i, |ε i| ≤ 1) :
    let M := blockDiagonal fun b => U b*realDiag (branchSpectrum K ε b)*(U b)ᴴ
    ((CFC.sqrt (Mᴴ*M)).trace).re ≤ 5/4 := by
  dsimp only
  rw [flagged_spectral_trace U (branchSpectrum K ε) hU]
  rw [Finset.sum_comm]
  simp_rw [Fintype.sum_bool]
  have hp : 0 < (Fintype.card I : ℝ) := by positivity
  simp only [branchSpectrum, Bool.false_eq_true, ite_false, ite_true, abs_mul, abs_of_nonneg (inv_nonneg.mpr hp.le),
    ← mul_add, ← Finset.mul_sum]
  have hb := flag_trace_bound K ε hK hm he
  calc
    _ ≤ (Fintype.card I : ℝ)⁻¹ * (5/4*(Fintype.card I : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hp.le)
      simpa only [add_comm] using hb
    _ = _ := by field_simp

end PairedOneBit
end

section
open Matrix
open scoped Kronecker

namespace PairedSpectralTrace

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
private theorem kprod_star (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    (A ⊗ₖ B)ᴴ=Aᴴ ⊗ₖ Bᴴ := by
  ext i j
  simp [Matrix.conjTranspose_apply]

private theorem kprod_isometric (U : Matrix I I ℂ) (V : Matrix J J ℂ)
    (hU : Uᴴ*U=1) (hV : Vᴴ*V=1) :
    (U ⊗ₖ V)ᴴ*(U ⊗ₖ V)=1 := by
  rw [kprod_star, ← Matrix.mul_kronecker_mul, hU, hV]
  exact Matrix.one_kronecker_one

/-- The exact matrix spectral provider is closed under tensoring recorded
Pauli sites, not only its eigenvalue signs as an abstract real transform. -/
private theorem kprod_spectral (U : Matrix I I ℂ) (V : Matrix J J ℂ)
    (f : I → ℝ) (g : J → ℝ) :
    (U*realDiag f*Uᴴ) ⊗ₖ (V*realDiag g*Vᴴ) =
      (U ⊗ₖ V)*realDiag (fun i : I × J => f i.1*g i.2)*(U ⊗ₖ V)ᴴ := by
  rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul, kprod_star]
  congr 2
  unfold realDiag
  rw [Matrix.diagonal_kronecker_diagonal]
  simp only [Complex.ofReal_mul]

end PairedSpectralTrace
end

section
namespace PairedBellSign

private theorem pt_eigenvector : ∀ a b x : I,
    pt a x 0 * quantumBell b 0 + pt a x 1 * quantumBell b 1 +
    pt a x 2 * quantumBell b 2 + pt a x 3 * quantumBell b 3 =
      bellSign a b * quantumBell b x := by decide

private theorem bell_basis_orthogonal : ∀ a b : I,
    quantumBell a 0 * quantumBell b 0 + quantumBell a 1 * quantumBell b 1 +
    quantumBell a 2 * quantumBell b 2 + quantumBell a 3 * quantumBell b 3 =
      if a=b then 2 else 0 := by decide

private theorem sign_rows_orthogonal : ∀ a b : I,
    bellSign a 0 * bellSign b 0 + bellSign a 1 * bellSign b 1 +
    bellSign a 2 * bellSign b 2 + bellSign a 3 * bellSign b 3 =
      if a=b then 4 else 0 := by decide

private theorem sign_mean : ∀ a : I, bellSign a 0 + bellSign a 1 + bellSign a 2 + bellSign a 3 = 2 := by decide

end PairedBellSign
end

section
open Matrix PairedBellSign
open scoped BigOperators

namespace PairedSpectralTrace

def Uraw : Matrix (Fin 4) (Fin 4) ℂ := fun x b => (quantumBell b x : ℂ)
def Araw (a : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ := fun x y => (pt a x y : ℂ)
def Usite : Matrix (Fin 4) (Fin 4) ℂ := (↑(Real.sqrt 2) : ℂ)⁻¹ • Uraw

private theorem raw_unitary : Urawᴴ*Uraw=(2:ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext a b
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  simp only [Uraw, Matrix.conjTranspose_apply, Complex.star_def, map_intCast,
    ← Int.cast_mul, ← Int.cast_add]
  rw [bell_basis_orthogonal]
  by_cases h : a=b
  · subst b; simp
  · simp [h]

private theorem unitary_site : Usiteᴴ*Usite=1 := by
  have h2 : (↑(Real.sqrt 2) : ℂ)^2=2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hp : (↑(Real.sqrt 2) : ℂ) ≠ 0 := by
    intro h
    rw [h] at h2
    norm_num at h2
  rw [Usite, conjTranspose_smul, Complex.star_def, map_inv₀, Complex.conj_ofReal,
    Matrix.smul_mul, Matrix.mul_smul, raw_unitary, smul_smul, smul_smul]
  have hc : (↑(Real.sqrt 2) : ℂ)⁻¹ * ((↑(Real.sqrt 2) : ℂ)⁻¹ * 2) = 1 := by
    field_simp
    linear_combination h2.symm
  rw [mul_assoc, hc, one_smul]

private theorem raw_site_eigen (a : Fin 4) :
    Araw a*Uraw = Uraw*diagonal (fun b => (bellSign a b : ℂ)) := by
  ext x b
  rw [Matrix.mul_apply, Fin.sum_univ_four, Matrix.mul_diagonal]
  simp only [Araw, Uraw, ← Int.cast_mul, ← Int.cast_add]
  rw [pt_eigenvector]
  simp [Int.cast_mul, mul_comm]

private theorem site_eigen (a : Fin 4) :
    ((1/2:ℂ) • Araw a)*Usite =
      Usite * realDiag (fun b => (bellSign a b : ℝ)/2) := by
  rw [Usite, Matrix.smul_mul, Matrix.mul_smul, raw_site_eigen, Matrix.smul_mul]
  rw [smul_comm]
  congr 1
  rw [← Matrix.mul_smul]
  congr 1
  ext i j
  by_cases h : i=j
  · subst j
    simp [realDiag]
    rw [div_eq_mul_inv, mul_comm]
  · simp [realDiag, h]

private theorem site_spectral (a : Fin 4) :
    ((1/2:ℂ) • Araw a) =
      Usite * realDiag (fun b => (bellSign a b : ℝ)/2) * Usiteᴴ := by
  have hu : Usite * Usiteᴴ = 1 := mul_eq_one_comm.mp unitary_site
  have he := congrArg (fun X : Matrix (Fin 4) (Fin 4) ℂ => X * Usiteᴴ) (site_eigen a)
  simpa only [Matrix.mul_assoc, hu, Matrix.mul_one] using he

end PairedSpectralTrace
end

section
open Matrix PairedTransform
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

namespace PairedSpectralTrace

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Sum of conditional Pauli projectors after partial transpose, indexed in
the original Hilbert-space basis, and still carrying the raw flag weights. -/
def recordedPT (P : I → Matrix I I ℂ) (h : I → ℝ) (z : ℝ) : Matrix I I ℂ :=
  ∑ j, (↑(z * h j) : ℂ) • P j

private theorem spectrum_mixture (P : I → Matrix I I ℂ) (U : Matrix I I ℂ)
    (K : I → I → ℝ) (h : I → ℝ) (z : ℝ)
    (hP : ∀ j, P j=U*realDiag (fun i => K i j)*Uᴴ) :
    recordedPT P h z =
      U * realDiag (fun i => z * applyKernel K h i) * Uᴴ := by
  unfold recordedPT
  simp_rw [hP]
  have hrewrite (j : I) :
      (↑(z*h j):ℂ) • (U*realDiag (fun i => K i j)*Uᴴ) =
      (U*((↑(z*h j):ℂ) • realDiag (fun i => K i j)))*Uᴴ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  simp_rw [hrewrite]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hd : (∑ j : I, (↑(z*h j):ℂ) • realDiag (fun i => K i j)) =
      realDiag (fun i => z*applyKernel K h i) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp only [realDiag, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.diagonal_apply_eq, ← Complex.ofReal_mul, ← Complex.ofReal_sum,
        applyKernel, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
    · simp [realDiag, Matrix.sum_apply, hij]
  rw [hd]

open PairedOneBit in
/-- Matrix-level cap for arbitrary stochastic paired Pauli records, once the
physical labels' common Bell spectral provider has been established. -/
private theorem physical_mixture_cap [Nonempty I] (P : I → Matrix I I ℂ) (U : Matrix I I ℂ)
    (K : I → I → ℝ) (ε : I → ℝ)
    (hU : Uᴴ*U=1)
    (hP : ∀ j, P j=U*realDiag (fun i => K i j)*Uᴴ)
    (hK : ∀ j k : I, ∑ i, K i j*K i k = if j=k then 1 else 0)
    (hm : ∀ i : I, ∑ j, K i j = 1) (he : ∀ i, |ε i| ≤ 1) :
    let M := blockDiagonal (fun b : Bool =>
      recordedPT P (fun j => (if b then 1+ε j else 1-ε j)/2) (Fintype.card I : ℝ)⁻¹)
    ((CFC.sqrt (Mᴴ*M)).trace).re ≤ 5/4 := by
  dsimp only
  simp_rw [spectrum_mixture P U K _ _ hP]
  exact physical_flag_bound (fun _ => U) K ε (fun _ => hU) hK hm he

open PairedOneBit in
private theorem mixture_fold_formula [Nonempty I] (P : I → Matrix I I ℂ) (U : Matrix I I ℂ)
    (K : I → I → ℝ) (ε : I → ℝ)
    (hU : Uᴴ*U=1)
    (hP : ∀ j, P j=U*realDiag (fun i => K i j)*Uᴴ)
    (hm : ∀ i : I, ∑ j, K i j = 1) :
    let M := blockDiagonal (fun b : Bool =>
      recordedPT P (fun j => (if b then 1+ε j else 1-ε j)/2) (Fintype.card I : ℝ)⁻¹)
    ((CFC.sqrt (Mᴴ*M)).trace).re =
      (Fintype.card I : ℝ)⁻¹ * ∑ i, max 1 |applyKernel K ε i| := by
  dsimp only
  simp_rw [spectrum_mixture P U K _ _ hP]
  rw [flagged_spectral_trace (fun _ : Bool => U)
    (fun b i => (Fintype.card I : ℝ)⁻¹ *
      applyKernel K (fun j => (if b then 1+ε j else 1-ε j)/2) i) (fun _ => hU)]
  rw [Finset.sum_comm]
  simp_rw [Fintype.sum_bool]
  have hp : 0 < (Fintype.card I : ℝ) := by positivity
  simp only [Bool.false_eq_true, ite_false, ite_true, abs_mul, abs_of_nonneg (inv_nonneg.mpr hp.le),
    ← mul_add, ← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [(complementary_blocks K ε hm i).1, (complementary_blocks K ε hm i).2,
    abs_div, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), ← add_div, abs_fold]

end PairedSpectralTrace
end

section
open Matrix PairedTensor PairedBellSign PairedTransform
open scoped BigOperators Kronecker

namespace PairedSpectralTrace

/-- Exact partial-transposed Pauli projectors in physical coordinates.
The coefficient basis is one common unitary, independent of the labels. -/
structure Packet (I : Type*) [Fintype I] [DecidableEq I] where
  basis : Matrix I I ℂ
  projectorPT : I → Matrix I I ℂ
  coeff : I → I → ℝ
  isometric : basisᴴ*basis=1
  spectral : ∀ j, projectorPT j=basis*realDiag (fun i => coeff i j)*basisᴴ
  columns : ∀ j k, ∑ i, coeff i j*coeff i k = if j=k then 1 else 0
  mean : ∀ i, ∑ j, coeff i j=1

def Packet.tensor {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Packet I) (B : Packet J) : Packet (I×J) where
  basis := A.basis ⊗ₖ B.basis
  projectorPT i := A.projectorPT i.1 ⊗ₖ B.projectorPT i.2
  coeff := PairedTensor.tensor A.coeff B.coeff
  isometric := kprod_isometric A.basis B.basis A.isometric B.isometric
  spectral i := by
    rw [A.spectral, B.spectral]
    exact kprod_spectral _ _ _ _
  columns := tensor_columns _ _ A.columns B.columns
  mean := tensor_mean _ _ A.mean B.mean

def signSite (a b : Fin 4) : ℝ := (bellSign a b : ℝ)/2

private theorem sign_symm : ∀ a b : Fin 4, bellSign a b=bellSign b a := by decide

private theorem site_columns (a b : Fin 4) :
    ∑ i, signSite i a * signSite i b = if a=b then 1 else 0 := by
  rw [Fin.sum_univ_four]
  simp only [signSite, (sign_symm 0 a), (sign_symm 0 b), (sign_symm 1 a), (sign_symm 1 b),
    (sign_symm 2 a), (sign_symm 2 b), (sign_symm 3 a), (sign_symm 3 b)]
  have h := congrArg (Int.cast : ℤ → ℝ) (sign_rows_orthogonal a b)
  push_cast at h
  split_ifs at h ⊢ <;> linarith

private theorem site_mean (a : Fin 4) : ∑ b, signSite a b=1 := by
  rw [Fin.sum_univ_four]
  simp only [signSite]
  have h := congrArg (Int.cast : ℤ → ℝ) (sign_mean a)
  push_cast at h
  linarith

def site : Packet (Fin 4) where
  basis := Usite
  projectorPT a := (1/2:ℂ) • Araw a
  coeff := signSite
  isometric := unitary_site
  spectral a := by simp_rw [signSite, sign_symm _ a]; exact site_spectral a
  columns := site_columns
  mean := site_mean

def physicalSites : (n : ℕ) → Packet (Sites n)
  | 0 => site
  | n+1 => site.tensor (physicalSites n)

open scoped ComplexOrder MatrixOrder in
private theorem arbitrary_site_cap (n : ℕ) (ε : Sites n → ℝ)
    (h : ∀ i, |ε i| ≤ 1) :
    let P := physicalSites n
    let M := blockDiagonal (fun b : Bool =>
      recordedPT P.projectorPT (fun j => (if b then 1+ε j else 1-ε j)/2)
        (Fintype.card (Sites n) : ℝ)⁻¹)
    ((CFC.sqrt (Mᴴ*M)).trace).re ≤ 5/4 := by
  let P := physicalSites n
  exact physical_mixture_cap P.projectorPT P.basis P.coeff ε
    P.isometric P.spectral P.columns P.mean h

def oneRecord (i : Fin 4) : ℝ := if i=0 then 1 else -1

private theorem one_record_spike (i : Fin 4) :
    applyKernel signSite oneRecord i = if i=3 then -2 else 0 := by
  fin_cases i <;>
    norm_num [applyKernel, Fin.sum_univ_four, signSite, oneRecord, bellSign, bitSign]

private theorem one_site_fold_sum : ∑ i, max 1 |applyKernel signSite oneRecord i| = 5 := by
  simp_rw [one_record_spike]
  norm_num [Fin.sum_univ_four, max_def]

def firstLabel : (n : ℕ) → Sites n → Fin 4
  | 0,i => i
  | _+1,i => i.1

def jointSingleton (n : ℕ) (i : Sites n) : ℝ := oneRecord (firstLabel n i)

private theorem jointSingleton_eval (n : ℕ) (i : Sites n) :
    applyKernel (physicalSites n).coeff (jointSingleton n) i =
      applyKernel signSite oneRecord (firstLabel n i) := by
  cases n with
  | zero => rfl
  | succ n =>
    change ∑ j : Fin 4 × Sites n,
      tensor signSite (physicalSites n).coeff i j * oneRecord j.1 = _
    have h := tensor_product_encoder signSite (physicalSites n).coeff oneRecord
      (fun _ => (1:ℝ)) i
    simp only [mul_one] at h
    rw [h, (physicalSites n).mean i.2, mul_one]
    rfl

open scoped ComplexOrder MatrixOrder in
private theorem arbitrary_site_optimum_attained (n : ℕ) :
    let P := physicalSites n
    let M := blockDiagonal (fun b : Bool =>
      recordedPT P.projectorPT (fun j =>
        (if b then 1+jointSingleton n j else 1-jointSingleton n j)/2)
        (Fintype.card (Sites n) : ℝ)⁻¹)
    ((CFC.sqrt (Mᴴ*M)).trace).re = 5/4 := by
  let P := physicalSites n
  dsimp only
  rw [mixture_fold_formula P.projectorPT P.basis P.coeff (jointSingleton n)
    P.isometric P.spectral P.mean]
  simp_rw [P, jointSingleton_eval]
  cases n with
  | zero =>
    change (Fintype.card (Fin 4) : ℝ)⁻¹ * (∑ i, max 1 |applyKernel signSite oneRecord i|) = _
    rw [one_site_fold_sum]
    norm_num
  | succ n =>
    change (Fintype.card (Fin 4 × Sites n) : ℝ)⁻¹ *
      (∑ i : Fin 4 × Sites n, max 1 |applyKernel signSite oneRecord i.1|) = _
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ,nsmul_eq_mul, ← Finset.mul_sum]
    rw [one_site_fold_sum, Fintype.card_prod]
    have h : (Fintype.card (Sites n) : ℝ) ≠ 0 := by positivity
    simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    field_simp

end PairedSpectralTrace
end

section
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure
open PairedSpectralTrace PairedBellSign Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

namespace LiteralPairedRibbon

def lostIndex (q:ℕ) : (↥(kept (q:=q))ᶜ) ≃ Fin (q+1) where
  toFun i := i.val.1
  invFun i := ⟨(i,1),by simp [kept]⟩
  left_inv i := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have h : i.val.2≠0 := by simpa [kept] using i.property
      apply Fin.ext
      have hn : i.val.2.val ≠ 0 := fun hh=>h (Fin.ext hh)
      change 1 = i.val.2.val
      omega
  right_inv _ := rfl

private theorem outcome_card (q:ℕ) :
    Fintype.card (Sites q) = Fintype.card (Bits (kept (q:=q))ᶜ) *
      Fintype.card (Bits (kept (q:=q))ᶜ) := by
  let e : (Fin (q+1)→K) ≃ Bits (kept (q:=q))ᶜ :=
    Equiv.arrowCongr (lostIndex q).symm (Equiv.refl K)
  let f := (splitCoords q).trans (e.prodCongr e)
  rw [Fintype.card_congr f, Fintype.card_prod]

def rawBorn {q:ℕ} (u:Fin (q+1)→Bool) (l:Sites q) : ℝ :=
  outcomeMass (mask (phaseForm u) kept) (lostVec (splitCoords q l).1) (lostVec (splitCoords q l).2)

private theorem rawBorn_uniform {q:ℕ} (u:Fin (q+1)→Bool) (l:Sites q) :
    rawBorn u l = (Fintype.card (Sites q):ℝ)⁻¹ := by
  rw [rawBorn,outcomeMass_eq,outcome_card]
  norm_cast

def swapRight {q:ℕ} (x y:Sites q) : Sites q :=
  (siteCoords q).symm (fun i=>fuse (firstBit (siteCoords q x i)) (secondBit (siteCoords q y i)))

private theorem local_PT (u:Bool) (l i j:Fin 4) :
    localAmplitude u l (fuse (firstBit i) (secondBit j)) *
     localAmplitude u l (fuse (firstBit j) (secondBit i)) = (pt l i j : ℝ)/2 := by
  have h := sign_sq (tau u*firstBit l*secondBit l)
  have hs : Real.sqrt 2 ^ 2 = 2 := by rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  have he (i j:Fin 4) :
      fuse (firstBit i) (secondBit j) = ⟨2*(i.val/2)+(j.val%2),by omega⟩ := by
    revert i j
    decide
  have ham := (PairedRibbonMask.literal_tensor_transport (fun _ : Fin 1=>u)).2
  rw [ham,ham, he i j, he j i]
  unfold pt
  push_cast
  calc
    _ = (sign (tau u*firstBit l*secondBit l)*sign (tau u*firstBit l*secondBit l)) *
      ((quantumBell l ⟨2*(i.val/2)+(j.val%2),by omega⟩ : ℝ) *
       (quantumBell l ⟨2*(j.val/2)+(i.val%2),by omega⟩ : ℝ)) / (Real.sqrt 2)^2 := by ring
    _ = _ := by rw [h,hs,one_mul]

def literalPT {q:ℕ} (u:Fin (q+1)→Bool) (l:Sites q) : Matrix (Sites q) (Sites q) ℂ :=
  fun x y => (↑(ribbonAmplitude u l (swapRight x y) * ribbonAmplitude u l (swapRight y x)):ℂ)

private theorem projectors_product (q:ℕ) (l i j:Sites q) :
    (physicalSites q).projectorPT l i j =
      ∏ k : Fin (q+1), (↑(pt (siteCoords q l k) (siteCoords q i k) (siteCoords q j k)) : ℂ)/2 := by
  induction q with
  | zero =>
    rw [Fin.prod_univ_one]
    change (1/2:ℂ) * (pt l i j : ℂ) = (pt l i j : ℂ)/2
    ring
  | succ q ih =>
    rw [Fin.prod_univ_succ]
    change ((1/2:ℂ)*(pt l.1 i.1 j.1 : ℂ)) *
        (physicalSites q).projectorPT l.2 i.2 j.2 =
      ((pt l.1 i.1 j.1 : ℂ)/2) *
        ∏ k : Fin (q+1), (↑(pt (siteCoords q l.2 k) (siteCoords q i.2 k) (siteCoords q j.2 k)):ℂ)/2
    rw [ih]
    congr 1
    ring
private theorem literal_physical_projector {q:ℕ} (u:Fin (q+1)→Bool) (l:Sites q) :
    literalPT u l = (physicalSites q).projectorPT l := by
  ext i j
  rw [literalPT,projectors_product]
  have h := (PairedRibbonMask.literal_tensor_transport u).1
  simp only [h, swapRight, Equiv.apply_symm_apply,
    ← Finset.prod_mul_distrib]
  simp_rw [local_PT, Complex.ofReal_prod, Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_ofNat]

def literalFlagMatrix {q:ℕ} (u:Fin (q+1)→Bool) (ε:Sites q→ℝ) :
    Matrix (Sites q × Bool) (Sites q × Bool) ℂ :=
  blockDiagonal fun b : Bool=>
    ∑ j, (↑(rawBorn u j * ((if b then 1+ε j else 1-ε j)/2)):ℂ) • (literalPT u j)

private theorem literalFlagMatrix_eq {q:ℕ} (u:Fin (q+1)→Bool) (ε:Sites q→ℝ) :
    literalFlagMatrix u ε = blockDiagonal (fun b : Bool =>
      recordedPT (physicalSites q).projectorPT (fun j => (if b then 1+ε j else 1-ε j)/2)
        (Fintype.card (Sites q) : ℝ)⁻¹) := by
  unfold literalFlagMatrix recordedPT
  simp only [rawBorn_uniform,literal_physical_projector]

private theorem actual_ribbon_one_bit_cap {q:ℕ} (u:Fin (q+1)→Bool) (ε:Sites q→ℝ) (h:∀ j, |ε j|≤1) :
    ((CFC.sqrt ((literalFlagMatrix u ε)ᴴ * literalFlagMatrix u ε)).trace).re ≤ 5/4 := by
  rw [literalFlagMatrix_eq]
  exact arbitrary_site_cap q ε h

end LiteralPairedRibbon
end

section
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure
open PairedSpectralTrace PairedBellSign PairedTransform Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace LiteralPairedRibbon

def bankBit (b:Bool) (j:Fin 4) : K := if b then firstBit j else secondBit j

def bank (q:ℕ) (b:Bool) (j:Sites q) : Fin (q+1)→K :=
  fun i=>bankBit b (siteCoords q j i)

private theorem bank_succ (q:ℕ) (b:Bool) (j:Sites (q+1)) :
    bank (q+1) b j = Fin.cons (bankBit b j.1) (bank q b j.2) := by
  funext i
  refine Fin.cases ?_ (fun a=>?_) i
  · rfl
  · rfl

private theorem bank_site (b:Bool) (f:K→ℝ) (i:Fin 4) :
    ∑ j, signSite i j * f (bankBit b j) = f (bankBit b i) := by
  rw [Fin.sum_univ_four]
  cases b <;> fin_cases i <;>
    norm_num [signSite,bellSign,bitSign,bankBit,firstBit,secondBit] <;> ring

private theorem separate_eigen (q:ℕ) (b:Bool) (f:(Fin (q+1)→K)→ℝ) (i:Sites q) :
    applyKernel (physicalSites q).coeff (fun j=>f (bank q b j)) i = f (bank q b i) := by
  induction q with
  | zero => exact bank_site b (fun k=>f (fun _=>k)) i
  | succ q ih =>
    change (∑ j : Sites (q+1), signSite i.1 j.1 * (physicalSites q).coeff i.2 j.2 *
          f (bank (q+1) b j)) = _
    simp_rw [bank_succ]
    change Fin 4 × Sites q at i
    change (∑ j : Fin 4 × Sites q, signSite i.1 j.1 * (physicalSites q).coeff i.2 j.2 *
          f (Fin.cons (bankBit b j.1) (bank q b j.2))) = _
    rw [Fintype.sum_prod_type]
    have H (j:Fin 4) :
        (∑ k:Sites q, signSite i.1 j * (physicalSites q).coeff i.2 k *
            f (Fin.cons (bankBit b j) (bank q b k))) =
          signSite i.1 j * f (Fin.cons (bankBit b j) (bank q b i.2)) := by
      simp only [mul_assoc]
      rw [← Finset.mul_sum]
      exact congrArg (signSite i.1 j * ·) (ih (fun a=>f (Fin.cons (bankBit b j) a)) i.2)
    simp_rw [H]
    exact bank_site b (fun a=>f (Fin.cons a (bank q b i.2))) i.1

private theorem physical_one_if_bounded_transform {q:ℕ} (u:Fin (q+1)→Bool) (ε:Sites q→ℝ)
    (h:∀ i, |applyKernel (physicalSites q).coeff ε i|≤1) :
    ((CFC.sqrt ((literalFlagMatrix u ε)ᴴ * literalFlagMatrix u ε)).trace).re = 1 := by
  rw [literalFlagMatrix_eq,mixture_fold_formula _ (physicalSites q).basis
    (physicalSites q).coeff ε (physicalSites q).isometric (physicalSites q).spectral
      (physicalSites q).mean]
  simp_rw [max_eq_left (h _)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hp : (Fintype.card (Sites q):ℝ) ≠ 0 := by positivity
  exact inv_mul_cancel₀ hp

/-- Arbitrary stochastic function of only one bank, not merely a linear parity. -/
private theorem actual_separate_bit_norm {q:ℕ} (u:Fin (q+1)→Bool) (b:Bool)
    (f:(Fin (q+1)→K)→ℝ) (hf:∀ a, |f a|≤1) :
    let M := literalFlagMatrix u (fun j=>f (bank q b j))
    ((CFC.sqrt (Mᴴ*M)).trace).re = 1 := by
  apply physical_one_if_bounded_transform
  intro i
  rw [separate_eigen]
  exact hf _

private theorem real_cast_sign (a:K) : (intSign a : ℝ)=sign a := by
  unfold intSign sign
  split_ifs <;> norm_num

def siteLin (a b:K) (j:Fin 4) : ℝ := sign (a*firstBit j+b*secondBit j)

private theorem siteLin_eigen_int : ∀ (a b:K) (i:Fin 4),
    ∑ j : Fin 4, bellSign i j * intSign (a*firstBit j+b*secondBit j) =
      2*intSign (a*b)*intSign (a*firstBit i+b*secondBit i) := by decide

private theorem siteLin_eigen (a b:K) (i:Fin 4) :
    applyKernel signSite (siteLin a b) i = sign (a*b)*siteLin a b i := by
  have h := congrArg (Int.cast:ℤ→ℝ) (siteLin_eigen_int a b i)
  push_cast at h
  simp only [real_cast_sign] at h
  unfold applyKernel siteLin signSite
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [h]
  ring

def recordPhase (q:ℕ) (a b:Fin (q+1)→K) (j:Sites q) : ℝ :=
  ∏ i, siteLin (a i) (b i) (siteCoords q j i)

private theorem phase_eigen (q:ℕ) (a b:Fin (q+1)→K) (i:Sites q) :
    applyKernel (physicalSites q).coeff (recordPhase q a b) i =
      (∏ j, sign (a j*b j)) * recordPhase q a b i := by
  induction q with
  | zero =>
    have H : recordPhase 0 a b = siteLin (a 0) (b 0) := by
      funext j
      unfold recordPhase
      rw [Fin.prod_univ_one]
      rfl
    rw [H, Fin.prod_univ_one]
    exact siteLin_eigen (a 0) (b 0) i
  | succ q ih =>
    let atail := fun j : Fin (q+1) => a j.succ
    let btail := fun j : Fin (q+1) => b j.succ
    have get (j:Sites (q+1)) : recordPhase (q+1) a b j =
        siteLin (a 0) (b 0) j.1 * recordPhase q atail btail j.2 := by
      unfold recordPhase
      rw [Fin.prod_univ_succ]
      rfl
    have hprod := PairedTensor.sum_product
      (fun j => signSite i.1 j * siteLin (a 0) (b 0) j)
      (fun j => (physicalSites q).coeff i.2 j * recordPhase q atail btail j)
    calc
      _ = ∑ j : Fin 4 × Sites q, (signSite i.1 j.1 * siteLin (a 0) (b 0) j.1) *
        ((physicalSites q).coeff i.2 j.2 * recordPhase q atail btail j.2) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [get]
          change (signSite i.1 j.1*(physicalSites q).coeff i.2 j.2) * _ = _
          ring
      _ = _ := by
        rw [hprod]
        change applyKernel signSite (siteLin (a 0) (b 0)) i.1 *
          applyKernel (physicalSites q).coeff (recordPhase q atail btail) i.2 = _
        have hp : (∏ j : Fin (q+1+1), sign (a j*b j)) =
            sign (a 0*b 0) * ∏ j : Fin (q+1), sign (atail j*btail j) :=
          Fin.prod_univ_succ _
        rw [siteLin_eigen, ih, get, hp]
        ring

private theorem sign_abs (a:K) : |sign a|=1 := by
  unfold sign
  split_ifs <;> norm_num

private theorem actual_pooled_linear_bit_norm {q:ℕ} (u:Fin (q+1)→Bool) (polarity:K)
    (a b:Fin (q+1)→K) :
    let M := literalFlagMatrix u (fun j=>sign polarity*recordPhase q a b j)
    ((CFC.sqrt (Mᴴ*M)).trace).re = 1 := by
  apply physical_one_if_bounded_transform
  intro i
  have h :
      applyKernel (physicalSites q).coeff (fun j=>sign polarity*recordPhase q a b j) i =
        sign polarity * applyKernel (physicalSites q).coeff (recordPhase q a b) i := by
    unfold applyKernel
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h, phase_eigen]
  unfold recordPhase siteLin
  simp only [abs_mul, Finset.abs_prod,sign_abs,Finset.prod_const_one,one_mul,le_refl]

end LiteralPairedRibbon
end

section
open LiteralPairedRibbon PairedSpectralTrace Matrix
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure
open scoped BigOperators ComplexOrder MatrixOrder

/-- Physical trace of the flagged partial transpose absolute operator, with
raw Born weights and in local right-Hadamard coordinates. -/
def flaggedValue {q : ℕ} (twist : Fin (q+1) → Bool) (record : Sites q → ℝ) : ℝ :=
  let M := literalFlagMatrix twist record
  ((CFC.sqrt (Mᴴ*M)).trace).re

/-- A fixed consecutive-interlaced ribbon mask on any nonempty finite packet
has optimal stochastic joint one-bit readout 5/4, attained deterministically.
For every fixed single bank and every coordinate affine linear encoding the
same physical flagged norm is 1. All erased twists are arbitrary. -/
theorem actual_joint_bit_gap {q : ℕ} (u : Fin (q+1) → Bool) :
    (∀ h : Sites q → ℝ, (∀ j, |h j| ≤ 1) → flaggedValue u h ≤ 5/4) ∧
    (∃ h : Sites q → ℝ, (∀ j, h j = 1 ∨ h j = -1) ∧ flaggedValue u h = 5/4) ∧
    (∀ (b : Bool) (f : (Fin (q+1) → K) → ℝ), (∀ x, |f x| ≤ 1) →
        flaggedValue u (fun j => f (bank q b j)) = 1) ∧
    (∀ (polarity : K) (a b : Fin (q+1) → K),
        flaggedValue u (fun j => sign polarity * recordPhase q a b j) = 1) := by
  refine ⟨fun h hh => actual_ribbon_one_bit_cap u h hh, ?_,
    fun b f hf => actual_separate_bit_norm u b f hf,
    fun polarity a b => actual_pooled_linear_bit_norm u polarity a b⟩
  refine ⟨jointSingleton q, ?_, ?_⟩
  · intro j
    unfold jointSingleton oneRecord
    split <;> simp
  · unfold flaggedValue
    rw [literalFlagMatrix_eq]
    exact arbitrary_site_optimum_attained q

end

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonOneBit
