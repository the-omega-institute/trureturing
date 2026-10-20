/- GID: D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPureBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPureBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Partial-transpose half bounds for arbitrary finite bipartite states. -/

/-
admission_basis: escape-witness
escape_witness: Pure.antisymmetric_product_bound
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19210
PetzSpectralCoordinates has no frozen state record; the spectral expansion uses
Mathlib Matrix.IsHermitian.spectral_theorem directly.
Direct frozen dependencies: none.
proof_shape: partialTransposeOn: bind-only; consumer: SymmetricAbsolutePPTPureBound.partialTranspose_sum, SymmetricAbsolutePPTPureBound.pure_state_half_bound, SymmetricAbsolutePPTPureBound.psd_partialTranspose_half_trace, SymmetricAbsolutePPTPermutationFloor.cross_partialTranspose_gram, SymmetricAbsolutePPTPermutationFloor.cross_partialTranspose_psd, SymmetricAbsolutePPTPermutationFloor.pt_split, SymmetricAbsolutePPTPermutationFloor.partialTranspose_PiS_sandwich, SymmetricAbsolutePPTPermutationFloor.partialTranspose_smulC, SymmetricAbsolutePPTPermutationFloor.partialTranspose_one, SymmetricAbsolutePPTPermutationFloor.P_partialTranspose_cosets, SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor, LouvetSymmetricAbsolutelyPPT.IsFullyPPT, LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: none.
proof_shape: partialTranspose_sum: bind-only; consumer: SymmetricAbsolutePPTPureBound.psd_partialTranspose_half_trace, SymmetricAbsolutePPTPermutationFloor.P_partialTranspose_cosets; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Pure.vec_norm_sq: bind-only; consumer: SymmetricAbsolutePPTPureBound.Pure.wedge_norm_bound, SymmetricAbsolutePPTPureBound.Pure.antisymmetric_product_bound; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Pure.mat_norm_sq: bind-only; consumer: SymmetricAbsolutePPTPureBound.Pure.wedge_norm_bound, SymmetricAbsolutePPTPureBound.Pure.antisymmetric_product_bound; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Pure.fmass_nonneg: bind-only; consumer: SymmetricAbsolutePPTPureBound.Pure.transpose_pairing_lower; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Pure.cross_sum: bind-only; consumer: SymmetricAbsolutePPTPureBound.Pure.wedge_mass; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Pure.wedge_mass: bind-only; consumer: SymmetricAbsolutePPTPureBound.Pure.wedge_norm_bound; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Pure.wedge_norm_bound: bind-only; consumer: SymmetricAbsolutePPTPureBound.Pure.antisymmetric_product_bound; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Pure.antisymmetric_product_bound: content; consumer: SymmetricAbsolutePPTPureBound.Pure.transpose_pairing_lower; escape_witness: SymmetricAbsolutePPTPureBound.Pure.antisymmetric_product_bound; Direct frozen dependencies: none.
proof_shape: Pure.transpose_pairing_identity: bind-only; consumer: SymmetricAbsolutePPTPureBound.Pure.transpose_pairing_lower; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Pure.transpose_pairing_lower: content; consumer: SymmetricAbsolutePPTPureBound.Pure.ptRank_lower; escape_witness: SymmetricAbsolutePPTPureBound.Pure.antisymmetric_product_bound; Direct frozen dependencies: none.
proof_shape: Pure.ptRank_hermitian: bind-only; consumer: SymmetricAbsolutePPTPureBound.Pure.ptRank_half_psd; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Pure.ptRank_form: bind-only; consumer: SymmetricAbsolutePPTPureBound.Pure.ptRank_lower; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Pure.ptRank_lower: content; consumer: SymmetricAbsolutePPTPureBound.Pure.ptRank_half_psd; escape_witness: SymmetricAbsolutePPTPureBound.Pure.antisymmetric_product_bound; Direct frozen dependencies: none.
proof_shape: Pure.ptRank_half_psd: content; consumer: SymmetricAbsolutePPTPureBound.pure_state_half_bound; escape_witness: SymmetricAbsolutePPTPureBound.Pure.antisymmetric_product_bound; Direct frozen dependencies: none.
proof_shape: splitWord_piecewise: bind-only; consumer: SymmetricAbsolutePPTPureBound.pure_state_half_bound; escape_witness: none; Direct frozen dependencies: none.
proof_shape: pure_state_half_bound: content; consumer: SymmetricAbsolutePPTPureBound.psd_partialTranspose_half_trace; escape_witness: SymmetricAbsolutePPTPureBound.Pure.antisymmetric_product_bound; Direct frozen dependencies: none.
proof_shape: compress_lower: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: none.
proof_shape: psd_partialTranspose_half_trace: content; consumer: LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: SymmetricAbsolutePPTPureBound.Pure.antisymmetric_product_bound; Direct frozen dependencies: none.
-/

import Mathlib.Analysis.Matrix.PosDef

namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound
open Matrix
open scoped BigOperators ComplexOrder
variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]
/-- Partial transposition on the sites in `S`: the `(x, y)` entry is the entry of `ρ` at the
labels with the `S` parts of `x` and `y` exchanged. -/
def partialTransposeOn {I L : Type*} [DecidableEq I] (S : Finset I)
    (ρ : Matrix (I → L) (I → L) ℂ) : Matrix (I → L) (I → L) ℂ :=
  fun x y => ρ (S.piecewise y x) (S.piecewise x y)


omit [Fintype I] [Fintype L] [DecidableEq L] in
lemma partialTranspose_sum {ι : Type*} (S : Finset I) (F : ι → Matrix (I → L) (I → L) ℂ)
    (s : Finset ι) : partialTransposeOn S (∑ i ∈ s, F i) = ∑ i ∈ s, partialTransposeOn S (F i) := by
  ext x y
  simp only [partialTransposeOn, Matrix.sum_apply]
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound

set_option maxHeartbeats 1000000
open scoped BigOperators Matrix ComplexOrder
open Matrix Complex WithLp
namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound.Pure
variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
private lemma vec_norm_sq (u : ι → ℂ) : ‖(toLp 2 u : EuclideanSpace ℂ _)‖ ^ 2 = (∑ i, Complex.normSq (u i)) := by
  simp [EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]
private lemma mat_norm_sq (M : Matrix α β ℂ) : ‖(toLp 2 (fun ij : α × β => M ij.1 ij.2) : EuclideanSpace ℂ _)‖ ^ 2 = (∑ i, ∑ j, Complex.normSq (M i j)) := by
  simp [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
    Complex.normSq_eq_norm_sq]
private lemma fmass_nonneg (M : Matrix α β ℂ) : 0 ≤ (∑ i, ∑ j, Complex.normSq (M i j)) := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _))
private lemma cross_sum (u v : β → ℂ) :
    (∑ i, ∑ j, (u i * v j * star (u j * v i)).re) =
      Complex.normSq (∑ i, star (u i) * v i) := by
  have hc : (∑ i, ∑ j, u i * v j * star (u j * v i)) =
      star (∑ i, star (u i) * v i) * (∑ i, star (u i) * v i) := by
    rw [star_sum, Finset.sum_mul]
    simp only [star_mul, star_star]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simpa only [Complex.re_sum, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re] using congrArg Complex.re hc
private lemma wedge_mass (u v : β → ℂ) :
    (∑ i, ∑ j, Complex.normSq ((fun i j => u i * v j - u j * v i) i j)) =
      2 * ((∑ i, Complex.normSq (u i)) * (∑ i, Complex.normSq (v i)) - Complex.normSq (∑ i, star (u i) * v i)) := by
  simp only [Complex.normSq_sub, Complex.normSq_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have hc := cross_sum u v
  simp only [Complex.star_def] at hc
  rw [hc]
  simp only [Complex.star_def]
  ring
private lemma wedge_norm_bound (u v : β → ℂ) :
    ‖(toLp 2 (fun ij : β × β => (fun i j => u i * v j - u j * v i) ij.1 ij.2) : EuclideanSpace ℂ _)‖ ≤
      Real.sqrt 2 * ‖(toLp 2 u : EuclideanSpace ℂ _)‖ * ‖(toLp 2 v : EuclideanSpace ℂ _)‖ := by
  have hsq := wedge_mass u v
  rw [← mat_norm_sq (fun i j => u i * v j - u j * v i),
    ← vec_norm_sq u, ← vec_norm_sq v] at hsq
  have hroot : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
  have hn := Complex.normSq_nonneg (∑ i, star (u i) * v i)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith [sq_nonneg (‖(toLp 2 u : EuclideanSpace ℂ _)‖ * ‖(toLp 2 v : EuclideanSpace ℂ _)‖)]

lemma antisymmetric_product_bound (V M : Matrix α β ℂ) :
    (∑ i, ∑ j, Complex.normSq ((fun i j => (Vᵀ * M) i j - (Vᵀ * M) j i) i j)) ≤ 2 * (∑ i, ∑ j, Complex.normSq (V i j)) * (∑ i, ∑ j, Complex.normSq (M i j)) := by
  let t : ℝ := ∑ a, ‖(toLp 2 (V a) : EuclideanSpace ℂ _)‖ * ‖(toLp 2 (M a) : EuclideanSpace ℂ _)‖
  have ht : 0 ≤ t := Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsum : (toLp 2 (fun ij : β × β => (fun i j => (Vᵀ * M) i j - (Vᵀ * M) j i) ij.1 ij.2) : EuclideanSpace ℂ _) =
      ∑ a, (toLp 2 (fun ij : β × β => (fun i j => V a i * M a j - V a j * M a i) ij.1 ij.2) : EuclideanSpace ℂ _) := by
    apply PiLp.ext
    intro ij
    simp [Matrix.mul_apply, Matrix.transpose_apply, ← toLp_sum,
      ← Finset.sum_sub_distrib]
  have hn : ‖(toLp 2 (fun ij : β × β => (fun i j => (Vᵀ * M) i j - (Vᵀ * M) j i) ij.1 ij.2) : EuclideanSpace ℂ _)‖ ≤ Real.sqrt 2 * t := by
    rw [hsum]
    calc
      ‖∑ a, (toLp 2 (fun ij : β × β => (fun i j => V a i * M a j - V a j * M a i) ij.1 ij.2) : EuclideanSpace ℂ _)‖ ≤
          ∑ a, ‖(toLp 2 (fun ij : β × β => (fun i j => V a i * M a j - V a j * M a i) ij.1 ij.2) : EuclideanSpace ℂ _)‖ := norm_sum_le _ _
      _ ≤ ∑ a, Real.sqrt 2 * ‖(toLp 2 (V a) : EuclideanSpace ℂ _)‖ * ‖(toLp 2 (M a) : EuclideanSpace ℂ _)‖ :=
          Finset.sum_le_sum (fun a _ => wedge_norm_bound (V a) (M a))
      _ = Real.sqrt 2 * t := by simp only [t, Finset.mul_sum, mul_assoc]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun a => ‖(toLp 2 (V a) : EuclideanSpace ℂ _)‖) (fun a => ‖(toLp 2 (M a) : EuclideanSpace ℂ _)‖)
  simp only [vec_norm_sq] at hc
  change t ^ 2 ≤ (∑ i, ∑ j, Complex.normSq (V i j)) * (∑ i, ∑ j, Complex.normSq (M i j)) at hc
  have hd := mul_self_le_mul_self (norm_nonneg _) hn
  rw [← pow_two, ← pow_two, mul_pow, Real.sq_sqrt zero_le_two] at hd
  rw [mat_norm_sq (fun i j => (Vᵀ * M) i j - (Vᵀ * M) j i)] at hd
  nlinarith
private lemma transpose_pairing_identity (Z : Matrix β β ℂ) :
    (∑ i, ∑ j, Complex.normSq ((fun i j => Z i j + Z j i) i j)) - (∑ i, ∑ j, Complex.normSq ((fun i j => Z i j - Z j i) i j)) =
      4 * ∑ i, ∑ j, (Z i j * star (Z j i)).re := by
  simp only [Complex.normSq_add, Complex.normSq_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Complex.star_def]
  ring
private lemma transpose_pairing_lower (V M : Matrix α β ℂ) :
    -((∑ i, ∑ j, Complex.normSq (V i j)) * (∑ i, ∑ j, Complex.normSq (M i j))) / 2 ≤
      ∑ i, ∑ j, ((Vᵀ * M) i j * star ((Vᵀ * M) j i)).re := by
  have hp := transpose_pairing_identity (Vᵀ * M)
  have hb := antisymmetric_product_bound V M
  have hn := fmass_nonneg (fun i j => (Vᵀ * M) i j + (Vᵀ * M) j i)
  nlinarith
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound.Pure
namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound.Pure
variable {α β : Type*} [Fintype α] [Fintype β]
omit [Fintype α] [Fintype β] in
private lemma ptRank_hermitian (ψ : α × β → ℂ) : (((Matrix.of (fun (x y : α × β) => (vecMulVec ψ (star ψ)) (y.1, x.2) (x.1, y.2))) : Matrix (α × β) (α × β) ℂ)).IsHermitian := by
  ext x y
  simp [Matrix.vecMulVec_apply, Pi.star_apply, Matrix.conjTranspose_apply, star_mul]
private lemma ptRank_form (ψ v : α × β → ℂ) :
    star v ⬝ᵥ (((Matrix.of (fun (x y : α × β) => (vecMulVec ψ (star ψ)) (y.1, x.2) (x.1, y.2))) : Matrix (α × β) (α × β) ℂ) *ᵥ v) =
      ∑ b : β, ∑ d : β,
        star ((((Matrix.of (fun a b => v (a,b))) : Matrix α β ℂ)ᵀ * ((Matrix.of (fun a b => ψ (a,b))) : Matrix α β ℂ)) b d) *
          ((((Matrix.of (fun a b => v (a,b))) : Matrix α β ℂ)ᵀ * ((Matrix.of (fun a b => ψ (a,b))) : Matrix α β ℂ)) d b) := by
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Matrix.vecMulVec_apply, Pi.star_apply, Pi.star_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  calc
    (∑ a : α, ∑ c : α, ∑ d : β, star (v (a,b)) *
        (ψ (c,b) * star (ψ (a,d)) * v (c,d))) =
        ∑ d : β, ∑ a : α, ∑ c : α, star (v (a,b)) *
          (ψ (c,b) * star (ψ (a,d)) * v (c,d)) := by
      calc
        _ = ∑ a : α, ∑ d : β, ∑ c : α, star (v (a,b)) *
            (ψ (c,b) * star (ψ (a,d)) * v (c,d)) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      rw [star_sum, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro c hc
      simp only [star_mul, Matrix.of_apply]
      ring
private lemma ptRank_lower (ψ v : α × β → ℂ) :
    -((∑ i, Complex.normSq (ψ i)) * (∑ i, Complex.normSq (v i))) / 2 ≤ (star v ⬝ᵥ (((Matrix.of (fun (x y : α × β) => (vecMulVec ψ (star ψ)) (y.1, x.2) (x.1, y.2))) : Matrix (α × β) (α × β) ℂ) *ᵥ v)).re := by
  rw [ptRank_form]
  simp only [Complex.re_sum]
  rw [Finset.sum_comm]
  have h := transpose_pairing_lower ((Matrix.of (fun a b => v (a,b))) : Matrix α β ℂ) (((Matrix.of (fun a b => ψ (a,b))) : Matrix α β ℂ))
  simp only [Fintype.sum_prod_type] at *
  convert h using 1
  · exact congrArg (fun t : ℝ => -t / 2) (mul_comm _ _)
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
private lemma ptRank_half_psd [DecidableEq α] [DecidableEq β]
    (ψ : α × β → ℂ) (hψ : (∑ i, Complex.normSq (ψ i)) = 1) :
    (((Matrix.of (fun (x y : α × β) => (vecMulVec ψ (star ψ)) (y.1, x.2) (x.1, y.2))) : Matrix (α × β) (α × β) ℂ) + (1 / 2 : ℝ) • (1 : Matrix (α × β) (α × β) ℂ)).PosSemidef := by
  have hh : (((Matrix.of (fun (x y : α × β) => (vecMulVec ψ (star ψ)) (y.1, x.2) (x.1, y.2))) : Matrix (α × β) (α × β) ℂ) + (1 / 2 : ℝ) • (1 : Matrix (α × β) (α × β) ℂ)).IsHermitian :=
    (ptRank_hermitian ψ).add (Matrix.isHermitian_one.smul (IsSelfAdjoint.div rfl rfl))
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
  intro v
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, ?_⟩
  · have hb := ptRank_lower ψ v
    rw [hψ, one_mul] at hb
    have hv : (star v ⬝ᵥ v).re = (∑ i, Complex.normSq (v i)) := by
      simp [dotProduct, ← Complex.normSq_eq_conj_mul_self]
    simpa only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_smul, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, hv] using (show 0 ≤ (star v ⬝ᵥ (((Matrix.of (fun (x y : α × β) => (vecMulVec ψ (star ψ)) (y.1, x.2) (x.1, y.2))) : Matrix (α × β) (α × β) ℂ) *ᵥ v)).re + (1 / 2 : ℝ) * (∑ i, Complex.normSq (v i)) by linarith)
  · exact (hh.im_star_dotProduct_mulVec_self v).symm
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound.Pure

namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound
open Matrix WithLp
variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]
omit [Fintype I] [Fintype L] [DecidableEq L] in
private lemma splitWord_piecewise (S : Finset I) (x y : I → L) :
    ((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).symm (((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L)) x).1, ((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L)) y).2) = S.piecewise x y := by
  funext i
  by_cases hi : i ∈ S <;>
    simp [Equiv.piEquivPiSubtypeProd, Finset.piecewise, hi]
private lemma pure_state_half_bound (S : Finset I) (ψ : (I → L) → ℂ)
    (hψ : ∑ x, Complex.normSq (ψ x) = 1) :
    (partialTransposeOn S (vecMulVec ψ (star ψ)) +
      (1/2 : ℝ) • (1 : Matrix (I → L) (I → L) ℂ)).PosSemidef := by
  let e := (Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))
  have hn : (∑ i, Complex.normSq ((ψ ∘ e.symm) i)) = 1 := by
    calc
      (∑ i, Complex.normSq ((ψ ∘ e.symm) i)) = ∑ x, Complex.normSq (ψ x) :=
        Equiv.sum_comp e.symm (fun x => Complex.normSq (ψ x))
      _ = 1 := hψ
  have h := (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound.Pure.ptRank_half_psd (ψ ∘ e.symm) hn).submatrix e
  convert h using 1
  ext x y
  simp only [Matrix.of_apply, Matrix.submatrix_add, Matrix.submatrix_smul,
    Matrix.submatrix_one_equiv, Matrix.add_apply, Matrix.smul_apply,
    Matrix.submatrix_apply, Matrix.vecMulVec_apply, Pi.star_apply, Function.comp_apply,
    e, splitWord_piecewise, partialTransposeOn, vecMulVec_apply, Pi.star_apply]
  simp only [Matrix.one_apply, ((Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L))).injective.eq_iff]
lemma compress_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A Q : Matrix ι ι ℂ) (a : ℝ)
    (hQ : Q.IsHermitian) (hQQ : Q * Q = Q) (hA : Q * A * Q = A)
    (h : (A + a • (1 : Matrix ι ι ℂ)).PosSemidef) :
    (A + a • Q).PosSemidef := by
  have hc := h.conjTranspose_mul_mul_same Q
  rwa [hQ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hQQ, hA] at hc
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound

namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound
open Matrix
attribute [local instance] Classical.propDecidable
variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]
lemma psd_partialTranspose_half_trace (S : Finset I)
    (A : Matrix (I → L) (I → L) ℂ) (hA : A.PosSemidef) :
    (partialTransposeOn S A + (A.trace.re/2) • (1 : Matrix (I → L) (I → L) ℂ)).PosSemidef := by
  let v (i : I → L) := fun x => hA.1.eigenvectorBasis i x
  have hu (i : I → L) : ∑ x, Complex.normSq (v i x) = 1 := by
    have he := hA.1.eigenvectorBasis.orthonormal.1 i
    have he2 := congrArg (· ^ 2) he
    rw [EuclideanSpace.norm_sq_eq] at he2
    simpa only [v, Complex.normSq_eq_norm_sq, one_pow] using he2
  have hexp : A = ∑ i, hA.1.eigenvalues i • vecMulVec (v i) (star (v i)) := by
    conv_lhs => rw [hA.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
    change (hA.1.eigenvectorUnitary : Matrix _ _ ℂ) *
      diagonal (Complex.ofReal ∘ hA.1.eigenvalues) *
      (hA.1.eigenvectorUnitary : Matrix _ _ ℂ)ᴴ = _
    ext x y
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      Function.comp_apply, RCLike.ofReal_eq_complex_ofReal, Complex.real_smul,
      smul_eq_mul, v]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have htr : A.trace.re = ∑ i, hA.1.eigenvalues i := by
    rw [hA.1.trace_eq_sum_eigenvalues]
    simp
  have hsum := Matrix.posSemidef_sum Finset.univ (fun i _ =>
    (pure_state_half_bound S (v i) (hu i)).smul (hA.eigenvalues_nonneg i))
  have he : (∑ i, hA.1.eigenvalues i •
      (partialTransposeOn S (vecMulVec (v i) (star (v i))) +
        (1/2 : ℝ) • (1 : Matrix (I → L) (I → L) ℂ))) =
      partialTransposeOn S A + (A.trace.re/2) • (1 : Matrix (I → L) (I → L) ℂ) := by
    conv_rhs => lhs; rw [hexp, partialTranspose_sum]
    simp only [smul_add, Finset.sum_add_distrib, smul_smul]
    congr 1
    rw [← Finset.sum_smul, htr, ← Finset.sum_mul]
    congr 1
    ring
  rwa [he] at hsum
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound
