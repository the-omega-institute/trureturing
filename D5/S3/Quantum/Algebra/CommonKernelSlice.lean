/- GID: D5/S3/Quantum/Algebra/CommonKernelSlice
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/CommonKernelSlice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A real coefficient combination realizes the common kernel of an adjoint-symmetric finite matrix family. -/

import D5.S3.Quantum.Algebra.CommonCoefficientPlane
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# Common-kernel slice machinery

For every finite family whose cross-Gram products are adjoint-symmetric, a
real coefficient combination has exactly the common kernel.  When that common
kernel is zero, the combination is injective and the input dimension is at
most the output dimension.  The width-three tensor theorem consumes these two
consequences in its kernel alternatives.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Module
open scoped BigOperators ComplexOrder ComplexConjugate InnerProductSpace

namespace D5.S3.Quantum.Algebra.CommonKernelSlice

private theorem orthogonal_from_two_kernels {a b : ℕ}
    (A B : Matrix (Fin a) (Fin b) ℂ) (hAB : Aᴴ * B = Bᴴ * A)
    (s t : ℝ) (hst : s ≠ t)
    (x y : Fin b → ℂ)
    (hx : (A + (s : ℂ) • B) *ᵥ x = 0)
    (hy : (A + (t : ℂ) • B) *ᵥ y = 0) :
    star (B *ᵥ x) ⬝ᵥ (B *ᵥ y) = 0 := by
  have hxs : A *ᵥ x = -(s : ℂ) • (B *ᵥ x) := by
    have h := eq_neg_of_add_eq_zero_left (by
      simpa only [Matrix.add_mulVec, Matrix.smul_mulVec] using hx)
    simpa only [neg_smul] using h
  have hyt : A *ᵥ y = -(t : ℂ) • (B *ᵥ y) := by
    have h := eq_neg_of_add_eq_zero_left (by
      simpa only [Matrix.add_mulVec, Matrix.smul_mulVec] using hy)
    simpa only [neg_smul] using h
  have he : star (A *ᵥ x) ⬝ᵥ (B *ᵥ y) =
      star (B *ᵥ x) ⬝ᵥ (A *ᵥ y) := by
    calc
      star (A *ᵥ x) ⬝ᵥ (B *ᵥ y) =
          star x ⬝ᵥ ((Aᴴ * B) *ᵥ y) :=
            (D5.S3.Quantum.Algebra.CommonCoefficientPlane.cross_pairing A B x y).symm
      _ = star x ⬝ᵥ ((Bᴴ * A) *ᵥ y) := by rw [hAB]
      _ = star (B *ᵥ x) ⬝ᵥ (A *ᵥ y) :=
        D5.S3.Quantum.Algebra.CommonCoefficientPlane.cross_pairing B A x y
  rw [hxs, hyt] at he
  rw [star_smul, star_neg, smul_dotProduct, dotProduct_smul] at he
  simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul] at he
  have h' : -(s : ℂ) * (star (B *ᵥ x) ⬝ᵥ (B *ᵥ y)) =
      -(t : ℂ) * (star (B *ᵥ x) ⬝ᵥ (B *ᵥ y)) := by
    simpa only [smul_eq_mul] using he
  have hstc : (s : ℂ) - (t : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hst
  have hz : ((s : ℂ) - (t : ℂ)) *
      (star (B *ᵥ x) ⬝ᵥ (B *ᵥ y)) = 0 := by
    linear_combination -h'
  exact (mul_eq_zero.mp hz).resolve_left hstc

private theorem dotProduct_orthogonal_family_linearIndependent {a : ℕ}
    {ι : Type*} [Fintype ι] (v : ι → Fin a → ℂ)
    (hne : ∀ i, v i ≠ 0)
    (horth : Pairwise fun i j => star (v i) ⬝ᵥ (v j) = 0) :
    LinearIndependent ℂ v := by
  let e := (WithLp.linearEquiv 2 ℂ (Fin a → ℂ)).symm
  apply LinearIndependent.of_comp e.toLinearMap
  refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun i => ?_) ?_
  · exact fun h => hne i (e.injective (h.trans e.map_zero.symm))
  · intro i j hij
    change inner ℂ (e (v i)) (e (v j)) = 0
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    exact horth hij

private theorem two_map_kernel_slice {a b : ℕ}
    (A B : Matrix (Fin a) (Fin b) ℂ)
    (hAB : Aᴴ * B = Bᴴ * A) :
    ∃ t : ℝ, ∀ x : Fin b → ℂ,
      (A + (t : ℂ) • B) *ᵥ x = 0 ↔ A *ᵥ x = 0 ∧ B *ᵥ x = 0 := by
  classical
  let p : Fin (a + 1) → ℝ := fun i => i.val
  let H (i : Fin (a + 1)) : Submodule ℂ (Fin b → ℂ) :=
    LinearMap.ker (A + (p i : ℂ) • B).mulVecLin
  let G (i : Fin (a + 1)) : (H i) →ₗ[ℂ] (Fin a → ℂ) :=
    B.mulVecLin.domRestrict (H i)
  let W (i : Fin (a + 1)) : Submodule ℂ (Fin a → ℂ) := LinearMap.range (G i)
  by_contra hbad
  have hnonzero : ∀ i, W i ≠ ⊥ := by
    intro i hi
    apply hbad
    refine ⟨p i, ?_⟩
    intro x
    constructor
    · intro hx
      have hxker : x ∈ H i := by
        change (A + (p i : ℂ) • B) *ᵥ x = 0
        exact hx
      refine ⟨?_, ?_⟩
      · change A *ᵥ x = 0
        have hzero : G i = 0 := LinearMap.range_eq_bot.mp hi
        have hz := congrArg (fun f : (H i) →ₗ[ℂ] (Fin a → ℂ) => f ⟨x, hxker⟩) hzero
        change B *ᵥ x = 0 at hz
        have hsum : A *ᵥ x + (p i : ℂ) • (B *ᵥ x) = 0 := by
          simpa only [Matrix.add_mulVec, Matrix.smul_mulVec] using hx
        rw [hz, smul_zero, add_zero] at hsum
        exact hsum
      · have hzero : B *ᵥ x = 0 := by
          have hzero : G i = 0 := LinearMap.range_eq_bot.mp hi
          have hz := congrArg (fun f : (H i) →ₗ[ℂ] (Fin a → ℂ) => f ⟨x, hxker⟩) hzero
          change B *ᵥ x = 0 at hz
          exact hz
        exact hzero
    · rintro ⟨hAx, hBx⟩
      simpa [Matrix.add_mulVec, Matrix.smul_mulVec, hAx, hBx]
  choose w hwmem hwne using fun i =>
    Submodule.exists_mem_ne_zero_of_ne_bot (hnonzero i)
  have hex : ∀ i, ∃ x : Fin b → ℂ, x ∈ H i ∧ B *ᵥ x = w i := by
    intro i
    rcases hwmem i with ⟨x, hx⟩
    refine ⟨x.1, x.2, ?_⟩
    change B *ᵥ x.1 = w i at hx
    exact hx
  choose x hxH hxB using hex
  have horth : Pairwise fun i j => star (w i) ⬝ᵥ (w j) = 0 := by
    intro i j hij
    have hxi : (A + (p i : ℂ) • B) *ᵥ x i = 0 := hxH i
    have hxj : (A + (p j : ℂ) • B) *ᵥ x j = 0 := hxH j
    have hh := orthogonal_from_two_kernels A B hAB (p i) (p j) (by
      intro he
      apply hij
      apply Fin.ext
      change (i.val : ℝ) = (j.val : ℝ) at he
      exact_mod_cast he) (x i) (x j) hxi hxj
    simpa only [hxB i, hxB j] using hh
  have hli : LinearIndependent ℂ w :=
    dotProduct_orthogonal_family_linearIndependent w hwne horth
  have hdim := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at hdim
  omega

private theorem common_kernel_slice_iff {k a b : ℕ}
    (X : Fin k → Matrix (Fin a) (Fin b) ℂ)
    (hcomm : ∀ i j, (X i)ᴴ * X j = (X j)ᴴ * X i) :
    ∃ t : Fin k → ℝ, ∀ x : Fin b → ℂ,
      (∑ i, (t i : ℂ) • X i) *ᵥ x = 0 ↔ ∀ i, X i *ᵥ x = 0 := by
  induction k with
  | zero =>
      refine ⟨fun i => Fin.elim0 i, ?_⟩
      intro x
      simp
  | succ k ih =>
      let Xt : Fin k → Matrix (Fin a) (Fin b) ℂ := fun i => X i.succ
      have htail : ∀ i j, (Xt i)ᴴ * Xt j = (Xt j)ᴴ * Xt i := by
        intro i j
        exact hcomm i.succ j.succ
      obtain ⟨u, hu⟩ := ih Xt htail
      let B : Matrix (Fin a) (Fin b) ℂ := ∑ i, (u i : ℂ) • Xt i
      have hAB : (X 0)ᴴ * B = Bᴴ * X 0 := by
        classical
        simp only [B, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]
        rw [Matrix.mul_sum, Matrix.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Matrix.mul_smul, Matrix.smul_mul, Complex.star_def,
          Complex.conj_ofReal]
        rw [hcomm 0 i.succ]
      obtain ⟨q, hq⟩ := two_map_kernel_slice (X 0) B hAB
      let t : Fin (k + 1) → ℝ := Fin.cases 1 (fun i => q * u i)
      have hsum : (∑ i : Fin (k + 1), (t i : ℂ) • X i) =
          X 0 + (q : ℂ) • B := by
        classical
        rw [Fin.sum_univ_succ]
        ext r c
        simp [t, Fin.cases_zero, Fin.cases_succ, B, Xt,
          Matrix.sum_apply, Matrix.smul_apply, Finset.smul_sum,
          Complex.ofReal_mul]
        ring
      have hBiff : ∀ x : Fin b → ℂ,
          B *ᵥ x = 0 ↔ ∀ i, Xt i *ᵥ x = 0 := by
        intro x
        simpa only [B] using hu x
      refine ⟨t, ?_⟩
      intro x
      rw [hsum]
      constructor
      · intro hx
        obtain ⟨h0, hB⟩ := (hq x).mp hx
        intro i
        refine Fin.cases h0 (fun j => ?_) i
        exact (hBiff x).mp hB j
      · intro hall
        apply (hq x).mpr
        refine ⟨hall 0, ?_⟩
        apply (hBiff x).mpr
        intro i
        exact hall i.succ

/-!
The coefficient family is real, and the conclusion is exact for every finite
family, including the empty and zero-dimensional cases.
-/
theorem common_kernel_slice {k a b : ℕ}
    (X : Fin k → Matrix (Fin a) (Fin b) ℂ)
    (hcomm : ∀ i j, (X i)ᴴ * X j = (X j)ᴴ * X i) :
    ∃ t : Fin k → ℝ,
      LinearMap.ker (∑ i, (t i : ℂ) • X i).mulVecLin =
        ⨅ i, LinearMap.ker (X i).mulVecLin := by
  obtain ⟨t, ht⟩ := common_kernel_slice_iff X hcomm
  refine ⟨t, ?_⟩
  ext x
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Submodule.mem_iInf]
  exact ht x

/-! The primitive branch uses this consequence when its common kernel is zero. -/
theorem common_kernel_slice_injective_of_common_kernel_bot {k a b : ℕ}
    (X : Fin k → Matrix (Fin a) (Fin b) ℂ)
    (hcomm : ∀ i j, (X i)ᴴ * X j = (X j)ᴴ * (X i))
    (hcommon : (⨅ i, LinearMap.ker (X i).mulVecLin) = ⊥) :
    ∃ t : Fin k → ℝ,
      Function.Injective (∑ i, (t i : ℂ) • X i).mulVecLin ∧ b ≤ a := by
  obtain ⟨t, ht⟩ := common_kernel_slice X hcomm
  have hker : LinearMap.ker (∑ i, (t i : ℂ) • X i).mulVecLin = ⊥ :=
    ht.trans hcommon
  have hinj : Function.Injective (∑ i, (t i : ℂ) • X i).mulVecLin :=
    LinearMap.ker_eq_bot.mp hker
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  have hdim' : b ≤ a := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hdim
  exact ⟨t, hinj, hdim'⟩

end D5.S3.Quantum.Algebra.CommonKernelSlice
