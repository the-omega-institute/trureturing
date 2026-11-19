/- GID: D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Regularity
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/PartialTransposeSaturation/Regularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel chains and nondegenerate bilinear pairings control the tensor ranks of regular pencils. -/

/- admission_basis: escape-witness -/

import D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Complex.Basic
import D5.S1.Eigenstructure.NilpotentJordanChains
import D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Rev

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Regular

open Module Matrix

private theorem exists_jordan_basis {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V) :
    ∃ (ι : Type) (s : ι → ℕ+) (μ : ι → ℂ)
      (b : Basis (Σ i, Fin (s i)) ℂ V),
      ∀ (i : ι) (j : Fin (s i)),
        f (b ⟨i, j⟩) = μ i • b ⟨i, j⟩ +
          if h : j.val + 1 < s i then b ⟨i, ⟨j.val + 1, h⟩⟩ else 0 := by
  classical
  let W := f.maxGenEigenspace
  let N (μ : ℂ) : Module.End ℂ (W μ) :=
    (f - algebraMap ℂ (Module.End ℂ V) μ).restrict
      (Module.End.mapsTo_maxGenEigenspace_of_comm
        (Algebra.mul_sub_algebraMap_commutes f μ) μ)
  have hn (μ : ℂ) : IsNilpotent (N μ) :=
    f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
  have chains := fun μ : ℂ =>
    D5.S1.Eigenstructure.NilpotentJordanChains.nilpotent_jordan_chains_rank (N μ) (hn μ)
  choose I hI s b hb hr using chains
  let d := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.independent_maxGenEigenspace f.iSup_maxGenEigenspace_eq_top
  let c := d.collectedBasis b
  refine ⟨(Σ μ, I μ), (fun i => s i.1 i.2), Sigma.fst,
    c.reindex (Equiv.sigmaAssoc (fun μ i => Fin (s μ i))).symm, ?_⟩
  rintro ⟨μ, i⟩ j
  have hh := congrArg Subtype.val (hb μ 1 i j)
  simp only [pow_one] at hh
  have hN (x : W μ) : (N μ x : V) = f x - μ • (x : V) := rfl
  rw [hN] at hh
  simp only [Basis.reindex_apply, Equiv.sigmaAssoc, Equiv.symm_symm,
    Equiv.coe_fn_mk, c, DirectSum.IsInternal.collectedBasis_coe]
  split_ifs with hj
  · have hh' : f (b μ ⟨i, j⟩ : V) - μ • (b μ ⟨i, j⟩ : V) =
        (b μ ⟨i, ⟨j.val + 1, hj⟩⟩ : V) := by
      simpa only [Nat.add_comm 1 j.val, dif_pos hj] using hh
    exact (sub_eq_iff_eq_add.mp hh').trans (add_comm _ _)
  · have hh' : f (b μ ⟨i, j⟩ : V) - μ • (b μ ⟨i, j⟩ : V) = 0 := by
      simpa only [Nat.add_comm 1 j.val, dif_neg hj, ZeroMemClass.coe_zero] using hh
    simpa using sub_eq_zero.mp hh'

private def chainReverse {ι : Type*} (s : ι → ℕ+) :
    Equiv.Perm (Σ i, Fin (s i)) :=
  Equiv.sigmaCongrRight fun i => Fin.revPerm

private def chainPairing {V ι : Type*} [AddCommGroup V] [Module ℂ V]
    (s : ι → ℕ+) [Finite (Σ i, Fin (s i))] [DecidableEq ι]
    (b : Basis (Σ i, Fin (s i)) ℂ V) : V ≃ₗ[ℂ] Module.Dual ℂ V :=
  b.equiv b.dualBasis (chainReverse s)

private theorem chainPairing_basis {V ι : Type*} [AddCommGroup V] [Module ℂ V]
    (s : ι → ℕ+) [Finite (Σ i, Fin (s i))] [DecidableEq ι]
    (b : Basis (Σ i, Fin (s i)) ℂ V)
    (i k : ι) (j : Fin (s i)) (l : Fin (s k)) :
    chainPairing s b (b ⟨i, j⟩) (b ⟨k, l⟩) =
      if h : i = k then if j.val + l.val + 1 = s i then 1 else 0 else 0 := by
  classical
  rw [chainPairing, Basis.equiv_apply, Basis.dualBasis_apply_self]
  by_cases hik : i = k
  · subst k
    simp only [chainReverse, Equiv.sigmaCongrRight_apply, Fin.revPerm_apply,
      Sigma.mk.inj_iff, heq_eq_eq, true_and, dif_pos rfl]
    have heq : l = j.rev ↔ j.val + l.val + 1 = s i := by
      rw [Fin.ext_iff, Fin.val_rev]
      have hj := j.isLt
      have hl := l.isLt
      omega
    simp [heq]
  · have hne : (⟨k, l⟩ : Σ i, Fin (s i)) ≠ chainReverse s ⟨i, j⟩ := by
      intro he
      exact hik (congrArg Sigma.fst he).symm
    simp [hne, hik]

/-- Every finite-dimensional complex endomorphism admits a nondegenerate
bilinear pairing with respect to which it is self-adjoint. The pairing reverses
actual Jordan chains; it is bilinear, not sesquilinear. -/
private theorem exists_selfAdjoint_pairing {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V) :
    ∃ e : V ≃ₗ[ℂ] Module.Dual ℂ V, ∀ x y, e (f x) y = e x (f y) := by
  classical
  obtain ⟨ι, s, μ, b, hb⟩ := exists_jordan_basis f
  letI := FiniteDimensional.fintypeBasisIndex b
  let e := chainPairing s b
  refine ⟨e, ?_⟩
  have he (i k : ι) (j : Fin (s i)) (l : Fin (s k)) :
      e (f (b ⟨i, j⟩)) (b ⟨k, l⟩) = e (b ⟨i, j⟩) (f (b ⟨k, l⟩)) := by
    rw [hb, hb]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul]
    by_cases hik : i = k
    · subst k
      by_cases hj : j.val + 1 < s i <;> by_cases hl : l.val + 1 < s i
      · simp only [dif_pos hj, dif_pos hl, e, chainPairing_basis, dif_pos rfl]
        <;> simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · simp only [dif_pos hj, dif_neg hl, map_zero, LinearMap.zero_apply,
          e, chainPairing_basis, dif_pos rfl, add_zero]
        have hn : ¬ (j.val + 1 + l.val + 1 = s i) := by
          have hl' := l.isLt
          omega
        simp [hn]
      · simp only [dif_neg hj, dif_pos hl, map_zero, LinearMap.zero_apply,
          e, chainPairing_basis, dif_pos rfl, add_zero]
        have hn : ¬ (j.val + (l.val + 1) + 1 = s i) := by
          have hj' := j.isLt
          omega
        simp [hn]
      · simp only [dif_neg hj, dif_neg hl, map_zero, LinearMap.zero_apply,
          e, chainPairing_basis, dif_pos rfl, add_zero]
    · simp only [e, chainPairing_basis, dif_neg hik]
      split_ifs <;> simp only [chainPairing_basis, dif_neg hik, map_zero,
        LinearMap.zero_apply, mul_zero, zero_add, add_zero]
  have hlin : (f.dualMap.comp e.toLinearMap) = e.toLinearMap.comp f := by
    apply b.ext
    rintro ⟨i, j⟩
    apply b.ext
    rintro ⟨k, l⟩
    exact (he i k j l).symm
  intro x y
  exact congrArg (fun g : Module.Dual ℂ V => g y) (LinearMap.congr_fun hlin x).symm

/-- Every square complex matrix has an invertible intertwiner with its transpose. -/
private theorem transpose_intertwiner {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) :
    ∃ S : Matrix n n ℂ, IsUnit S.det ∧ Hᵀ * S = S * H := by
  classical
  obtain ⟨e, he⟩ := exists_selfAdjoint_pairing H.mulVecLin
  let b := Pi.basisFun ℂ n
  let S := LinearMap.toMatrix b b.dualBasis e.toLinearMap
  let T := LinearMap.toMatrix b.dualBasis b e.symm.toLinearMap
  have hTS : T * S = 1 := by
    dsimp [T, S]
    rw [← LinearMap.toMatrix_comp b b.dualBasis b]
    have hh : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext; simp
    rw [hh, LinearMap.toMatrix_id]
  have hdet : IsUnit S.det := Matrix.isUnit_det_of_left_inverse hTS
  refine ⟨S, hdet, ?_⟩
  have hf : H.mulVecLin.dualMap.comp e.toLinearMap =
      e.toLinearMap.comp H.mulVecLin := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact (he x y).symm
  have hm := congrArg (LinearMap.toMatrix b b.dualBasis) hf
  rw [LinearMap.toMatrix_comp b b.dualBasis b.dualBasis,
    LinearMap.toMatrix_comp b b b.dualBasis] at hm
  have hH : LinearMap.toMatrix b b H.mulVecLin = H := by
    change LinearMap.toMatrix' (Matrix.toLin' H) = H
    exact LinearMap.toMatrix'_toLin' H
  have ht : LinearMap.toMatrix b.dualBasis b.dualBasis H.mulVecLin.dualMap = Hᵀ := by
    rw [LinearMap.dualMap_def, LinearMap.toMatrix_transpose, hH]
  simpa only [ht, hH] using hm


/-- A pair with an invertible scalar combination is simultaneously equivalent
to its transposed pair. The same two changes of basis work for both matrices. -/
private theorem pair_transpose_equivalent {n : Type*} [Fintype n] [DecidableEq n]
    (A₁ A₂ : Matrix n n ℂ) (t : ℂ) (hC : IsUnit (A₁ + t • A₂).det) :
    ∃ P Q : Matrix n n ℂ, IsUnit P.det ∧ IsUnit Q.det ∧
      P * A₁ * Q = A₁ᵀ ∧ P * A₂ * Q = A₂ᵀ := by
  classical
  let C := A₁ + t • A₂
  let H := C⁻¹ * A₂
  obtain ⟨S, hS, hSH⟩ := transpose_intertwiner H
  let P := S * C⁻¹
  let Q := S⁻¹ * Cᵀ
  have hP : IsUnit P.det := by
    dsimp [P]
    rw [Matrix.det_mul]
    exact hS.mul (Matrix.isUnit_nonsing_inv_det C hC)
  have hQ : IsUnit Q.det := by
    dsimp [Q]
    rw [Matrix.det_mul]
    exact (Matrix.isUnit_nonsing_inv_det S hS).mul (Matrix.isUnit_det_transpose C hC)
  have hCH : C * H = A₂ := by
    dsimp [H]
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv C hC, Matrix.one_mul]
  have hC' : P * C * Q = Cᵀ := by
    dsimp [P, Q]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc C⁻¹ C, Matrix.nonsing_inv_mul C hC, Matrix.one_mul,
      ← Matrix.mul_assoc S S⁻¹, Matrix.mul_nonsing_inv S hS, Matrix.one_mul]
  have hA₂ : P * A₂ * Q = A₂ᵀ := by
    dsimp [P, Q]
    calc
      S * C⁻¹ * A₂ * (S⁻¹ * Cᵀ) = (S * H) * S⁻¹ * Cᵀ := by
        simp only [H, Matrix.mul_assoc]
      _ = (Hᵀ * S) * S⁻¹ * Cᵀ := by rw [hSH]
      _ = Hᵀ * Cᵀ := by
        rw [Matrix.mul_assoc Hᵀ S S⁻¹, Matrix.mul_nonsing_inv S hS, Matrix.mul_one]
      _ = A₂ᵀ := by rw [← Matrix.transpose_mul, hCH]
  refine ⟨P, Q, hP, hQ, ?_, hA₂⟩
  have he : A₁ = C - t • A₂ := by dsimp [C]; abel
  rw [he, Matrix.mul_sub, Matrix.sub_mul, mul_smul_comm, smul_mul_assoc, hC', hA₂]
  simp [C]


/-- A regular first-factor pair has the same tensor rank before and after
partial transposition, for every rectangular second-factor pair. -/
private theorem rank_partialTranspose_of_regular {n p q : Type*}
    [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (A₁ A₂ : Matrix n n ℂ) (B₁ B₂ : Matrix p q ℂ)
    (t : ℂ) (hC : IsUnit (A₁ + t • A₂).det) :
    (partialTranspose A₁ A₂ B₁ B₂).rank = (tensorSum A₁ A₂ B₁ B₂).rank := by
  obtain ⟨P, Q, hP, hQ, h₁, h₂⟩ := pair_transpose_equivalent A₁ A₂ t hC
  simpa only [h₁, h₂, Matrix.one_mul, Matrix.mul_one, partialTranspose] using
    rank_tensorSum_change A₁ A₂ B₁ B₂ P Q 1 1 hP hQ (by simp) (by simp)

end D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Regular


namespace D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Regularity

open Matrix Polynomial Module
open D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The polynomial pencil uses the same sign convention as `boundary`. -/
private def polynomialPencil (A B : Matrix n n ℂ) : Matrix n n ℂ[X] :=
  fun i j => C (A i j) - X * C (B i j)

private theorem polynomial_kernel_chain (A B : Matrix n n ℂ)
    (v : n → ℂ[X]) (hv : v ≠ 0) (hker : polynomialPencil A B *ᵥ v = 0) :
    ∃ (r : ℕ) (u : Fin (r + 1) → n → ℂ),
      boundary A.mulVecLin B.mulVecLin (r + 1) u = 0 ∧ u (Fin.last r) ≠ 0 := by
  classical
  let S := Finset.univ.filter (fun j : n => v j ≠ 0)
  have hS : S.Nonempty := by
    by_contra h
    apply hv
    funext j
    by_contra hj
    have hj' : v j ≠ 0 := by simpa using hj
    exact h ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj'⟩⟩
  obtain ⟨j₀, hj₀, hmax⟩ := Finset.exists_mem_eq_sup S hS (fun j => (v j).natDegree)
  have hv₀ : v j₀ ≠ 0 := (Finset.mem_filter.mp hj₀).2
  let r := (v j₀).natDegree
  let c : ℕ → n → ℂ := fun k j => (v j).coeff k
  let u : Fin (r + 1) → n → ℂ := fun k => c k.val
  have hbound (j : n) (hj : v j ≠ 0) : (v j).natDegree ≤ r := by
    have h := Finset.le_sup (f := fun j => (v j).natDegree) (by simp [S, hj] : j ∈ S)
    exact h.trans_eq hmax
  have hhigh : c (r + 1) = 0 := by
    funext j
    by_cases hj : v j = 0
    · simp [c, hj]
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hbound j hj; omega)
  have hzero (i : n) : (A *ᵥ c 0) i = 0 := by
    have hh := congrArg (fun p : ℂ[X] => p.coeff 0) (congrFun hker i)
    simpa [Matrix.mulVec, dotProduct, polynomialPencil, sub_mul, mul_assoc,
      Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, c] using hh
  have hsucc (i : n) (k : ℕ) : (A *ᵥ c (k + 1)) i - (B *ᵥ c k) i = 0 := by
    have hh := congrArg (fun p : ℂ[X] => p.coeff (k + 1)) (congrFun hker i)
    simpa [Matrix.mulVec, dotProduct, polynomialPencil, sub_mul, mul_assoc,
      Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul,
      Finset.sum_sub_distrib, c] using hh
  refine ⟨r, u, ?_, ?_⟩
  · ext k i
    cases k using Fin.lastCases with
    | last =>
        have hh := hsucc i r
        rw [hhigh, Matrix.mulVec_zero, Pi.zero_apply] at hh
        simpa [boundary, u, Function.comp_def, Matrix.mulVecLin_apply] using hh
    | cast k =>
        cases k using Fin.cases with
        | zero =>
            simpa [boundary, u, Function.comp_def, Matrix.mulVecLin_apply,
              Fin.snoc_apply_zero] using hzero i
        | succ k =>
            change (Fin.snoc (α := fun _ => n → ℂ)
                (A.mulVecLin ∘ u) 0 k.succ.castSucc) i -
              (Fin.cons (α := fun _ => n → ℂ)
                0 (B.mulVecLin ∘ u) k.succ.castSucc) i = 0
            rw [Fin.snoc_castSucc, Fin.castSucc_succ, Fin.cons_succ]
            exact hsucc i k.val
  · intro h
    have hh := congrFun h j₀
    apply (Polynomial.leadingCoeff_ne_zero.mpr hv₀)
    simpa [u, c, r, Polynomial.coeff_natDegree] using hh

/-- A square pencil with no nonzero right kernel chain has a nonzero determinant
polynomial. This uses the integral-domain kernel theorem directly, without
introducing a rational-function field. -/
private theorem determinant_ne_zero_of_chain_free (A B : Matrix n n ℂ)
    (hfree : ∀ (r : ℕ) (u : Fin (r + 1) → n → ℂ),
      boundary A.mulVecLin B.mulVecLin (r + 1) u = 0 → u (Fin.last r) = 0) :
    (polynomialPencil A B).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨r, u, hu, hlast⟩ := polynomial_kernel_chain A B v hv hker
  exact hlast (hfree r u hu)

/-- A square pencil with no polynomial right kernel admits an invertible scalar
combination over the complex numbers. -/
private theorem exists_invertible_combination (A B : Matrix n n ℂ)
    (hfree : ∀ (r : ℕ) (u : Fin (r + 1) → n → ℂ),
      boundary A.mulVecLin B.mulVecLin (r + 1) u = 0 → u (Fin.last r) = 0) :
    ∃ t : ℂ, IsUnit (A + t • B).det := by
  classical
  have hd := determinant_ne_zero_of_chain_free A B hfree
  have hex : ∃ t : ℂ, (polynomialPencil A B).det.eval t ≠ 0 := by
    by_contra h
    push_neg at h
    apply hd
    exact Polynomial.funext (fun t => by simpa using h t)
  obtain ⟨t, ht⟩ := hex
  refine ⟨-t, isUnit_iff_ne_zero.mpr ?_⟩
  have hmap : (polynomialPencil A B).map (Polynomial.evalRingHom t) = A + (-t) • B := by
    ext i j
    simp only [Matrix.map_apply, polynomialPencil, Polynomial.coe_evalRingHom,
      Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have he : (polynomialPencil A B).det.eval t = (A + (-t) • B).det := by
    change (Polynomial.evalRingHom t) (polynomialPencil A B).det = _
    rw [RingHom.map_det]
    change ((polynomialPencil A B).map (Polynomial.evalRingHom t)).det = _
    rw [hmap]
  exact he ▸ ht

section Coordinates

variable {U V : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V]

/-- The absence of polynomial kernel chains is independent of coordinates. -/
private theorem chain_free_toMatrix (bu : Basis n ℂ U) (bv : Basis n ℂ V)
    (f g : U →ₗ[ℂ] V)
    (hfree : ∀ (r : ℕ) (u : Fin (r + 1) → U),
      boundary f g (r + 1) u = 0 → u (Fin.last r) = 0) :
    ∀ (r : ℕ) (u : Fin (r + 1) → n → ℂ),
      boundary (LinearMap.toMatrix bu bv f).mulVecLin
        (LinearMap.toMatrix bu bv g).mulVecLin (r + 1) u = 0 →
      u (Fin.last r) = 0 := by
  intro r u hu
  let x : Fin (r + 1) → U := fun k => bu.equivFun.symm (u k)
  have hm (a : U →ₗ[ℂ] V) (k : Fin (r + 1)) :
      LinearMap.toMatrix bu bv a *ᵥ u k = bv.equivFun (a (x k)) := by
    have h := LinearMap.toMatrix_mulVec_repr bu bv a (x k)
    simpa only [← Basis.equivFun_apply, x, LinearEquiv.apply_symm_apply] using h
  have hn (a : U →ₗ[ℂ] V) : bv.equivFun.symm ∘
      ((LinearMap.toMatrix bu bv a).mulVecLin ∘ u) = a ∘ x := by
    funext k
    change bv.equivFun.symm (LinearMap.toMatrix bu bv a *ᵥ u k) = a (x k)
    rw [hm, LinearEquiv.symm_apply_apply]
  have hz : boundary f g (r + 1) x = 0 := by
    have he : Fin.snoc ((LinearMap.toMatrix bu bv f).mulVecLin ∘ u) 0 =
        (@Fin.cons _ (fun _ => n → ℂ)) 0
          ((LinearMap.toMatrix bu bv g).mulVecLin ∘ u) := sub_eq_zero.mp hu
    have he' := congrArg (fun v : Fin (r + 2) → n → ℂ => bv.equivFun.symm ∘ v) he
    rw [Fin.comp_snoc, Fin.comp_cons] at he'
    simp only [map_zero, hn] at he'
    exact sub_eq_zero.mpr he'
  have hx := hfree r x hz
  have hh := congrArg bu.equivFun hx
  simpa only [x, LinearEquiv.apply_symm_apply, map_zero] using hh

/-- A chain-free square pair admits an invertible scalar combination in any
two choices of bases. -/
private theorem exists_invertible_toMatrix_combination (bu : Basis n ℂ U) (bv : Basis n ℂ V)
    (f g : U →ₗ[ℂ] V)
    (hfree : ∀ (r : ℕ) (u : Fin (r + 1) → U),
      boundary f g (r + 1) u = 0 → u (Fin.last r) = 0) :
    ∃ t : ℂ, IsUnit
      (LinearMap.toMatrix bu bv f + t • LinearMap.toMatrix bu bv g).det :=
  exists_invertible_combination _ _ (chain_free_toMatrix bu bv f g hfree)

/-- A chain-free pair between spaces with equally indexed bases has a
bijective scalar combination. -/
private theorem exists_bijective_combination_of_bases (bu : Basis n ℂ U) (bv : Basis n ℂ V)
    (f g : U →ₗ[ℂ] V)
    (hfree : ∀ (r : ℕ) (u : Fin (r + 1) → U),
      boundary f g (r + 1) u = 0 → u (Fin.last r) = 0) :
    ∃ t : ℂ, Function.Bijective (f + t • g) := by
  obtain ⟨t, ht⟩ := exists_invertible_toMatrix_combination bu bv f g hfree
  let C := LinearMap.toMatrix bu bv f + t • LinearMap.toMatrix bu bv g
  have hb : Function.Bijective C.mulVecLin := by
    change Function.Bijective (Matrix.toLin' C)
    exact (Matrix.toLinearEquiv (Pi.basisFun ℂ n) C ht).bijective
  have hc (x : U) : C *ᵥ bu.equivFun x = bv.equivFun ((f + t • g) x) := by
    have h := LinearMap.toMatrix_mulVec_repr bu bv (f + t • g) x
    simpa only [map_add, map_smul, ← Basis.equivFun_apply, C] using h
  refine ⟨t, ?_, ?_⟩
  · intro x y hxy
    apply bu.equivFun.injective
    apply hb.1
    change C *ᵥ bu.equivFun x = C *ᵥ bu.equivFun y
    rw [hc, hc, hxy]
  · intro y
    obtain ⟨x, hx⟩ := hb.2 (bv.equivFun y)
    refine ⟨bu.equivFun.symm x, bv.equivFun.injective ?_⟩
    rw [← hc, LinearEquiv.apply_symm_apply]
    exact hx

end Coordinates

open ChainSplitting.FinitePair

/-- The final square leaf of a two-sided chain reduction is a regular pencil. -/
private theorem exists_bijective_combination (p : Pencil ℂ) (hp : RightReduced p)
    (hsquare : Module.finrank ℂ p.domain = Module.finrank ℂ p.codomain) :
    ∃ t : ℂ, Function.Bijective (p.first + t • p.second) := by
  classical
  let bu := Module.finBasis ℂ p.domain
  let bv := Module.finBasisOfFinrankEq ℂ p.codomain hsquare.symm
  exact exists_bijective_combination_of_bases bu bv p.first p.second hp

/-- A square chain-free first factor contributes equal tensor ranks before
and after dualizing that factor, for every finite-dimensional second pair. -/
theorem tensor_rank_dual_eq_of_reduced (p q : Pencil ℂ) (hp : RightReduced p)
    (hsquare : Module.finrank ℂ p.domain = Module.finrank ℂ p.codomain) :
    Module.finrank ℂ (LinearMap.range
      (TensorProduct.map p.first.dualMap q.first +
        TensorProduct.map p.second.dualMap q.second)) =
      Module.finrank ℂ (LinearMap.range
        (TensorProduct.map p.first q.first + TensorProduct.map p.second q.second)) := by
  classical
  let bu := Module.finBasis ℂ p.domain
  let bv := Module.finBasisOfFinrankEq ℂ p.codomain hsquare.symm
  let bqu := Module.finBasis ℂ q.domain
  let bqv := Module.finBasis ℂ q.codomain
  obtain ⟨t, ht⟩ := exists_invertible_toMatrix_combination bu bv p.first p.second hp
  rw [finrank_tensorSum_toMatrix bv.dualBasis bu.dualBasis bqu bqv,
    finrank_tensorSum_toMatrix bu bv bqu bqv]
  simp only [LinearMap.dualMap_def, LinearMap.toMatrix_transpose]
  change (partialTranspose (LinearMap.toMatrix bu bv p.first)
    (LinearMap.toMatrix bu bv p.second) (LinearMap.toMatrix bqu bqv q.first)
    (LinearMap.toMatrix bqu bqv q.second)).rank = _
  exact Regular.rank_partialTranspose_of_regular _ _ _ _ t ht

/-- Independence of the second pair detects both maps in the first pair. -/
private theorem tensor_eq_zero_iff_of_independent_right (p q : Pencil ℂ)
    (hq : LinearIndependent ℂ ![q.first, q.second]) :
    TensorProduct.map p.first q.first + TensorProduct.map p.second q.second = 0 ↔
      p.first = 0 ∧ p.second = 0 := by
  classical
  let bu := Module.finBasis ℂ p.domain
  let bv := Module.finBasis ℂ p.codomain
  let bqu := Module.finBasis ℂ q.domain
  let bqv := Module.finBasis ℂ q.codomain
  let M := LinearMap.toMatrix bu bv
  let N := LinearMap.toMatrix bqu bqv
  have hqi : LinearIndependent ℂ ![N q.first, N q.second] := by
    convert hq.map' N.toLinearMap (LinearMap.ker_eq_bot.mpr N.injective) using 1
    ext i
    fin_cases i <;> rfl
  constructor
  · intro hz
    have hm := congrArg
      (LinearMap.toMatrix (bu.tensorProduct bqu) (bv.tensorProduct bqv)) hz
    have hm' : tensorSum (M p.first) (M p.second) (N q.first) (N q.second) = 0 := by
      simpa only [map_add, map_zero, TensorProduct.toMatrix_map, tensorSum, M, N] using hm
    have hs : tensorSum (N q.first) (N q.second) (M p.first) (M p.second) = 0 := by
      ext ⟨i, k⟩ ⟨j, l⟩
      have h := congrFun (congrFun hm' (k, i)) (l, j)
      simpa only [tensorSum, Matrix.add_apply, Matrix.kroneckerMap_apply, mul_comm,
        Matrix.zero_apply] using h
    have hp := (tensorSum_eq_zero_iff _ _ _ _ hqi).mp hs
    exact ⟨M.injective (by simpa using hp.1), M.injective (by simpa using hp.2)⟩
  · rintro ⟨hf, hg⟩
    simp only [hf, hg, TensorProduct.map_zero_left, zero_add]

/-- A nonzero pair tensored against an independent pair has positive rank. -/
private theorem tensor_rank_pos_of_independent_right (p q : Pencil ℂ)
    (hq : LinearIndependent ℂ ![q.first, q.second])
    (hp : ¬ (p.first = 0 ∧ p.second = 0)) :
    0 < Module.finrank ℂ (LinearMap.range
      (TensorProduct.map p.first q.first + TensorProduct.map p.second q.second)) := by
  by_contra h
  have hr := Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_not_pos h)
  have hz := LinearMap.range_eq_bot.mp hr
  exact hp ((tensor_eq_zero_iff_of_independent_right p q hq).mp hz)

/-- Every positive-dimensional regular leaf has strictly positive tensor rank
against an independent second pair. -/
theorem tensor_rank_pos_of_reduced (p q : Pencil ℂ) (hp : RightReduced p)
    (hsquare : Module.finrank ℂ p.domain = Module.finrank ℂ p.codomain)
    (hd : 0 < Module.finrank ℂ p.domain)
    (hq : LinearIndependent ℂ ![q.first, q.second]) :
    0 < Module.finrank ℂ (LinearMap.range
      (TensorProduct.map p.first q.first + TensorProduct.map p.second q.second)) := by
  apply tensor_rank_pos_of_independent_right p q hq
  rintro ⟨hf, hg⟩
  obtain ⟨t, ht⟩ := exists_bijective_combination p hp hsquare
  letI := Module.nontrivial_of_finrank_pos hd
  obtain ⟨x, hx⟩ := exists_ne (0 : p.domain)
  apply hx
  apply ht.1
  simp only [hf, hg, smul_zero, add_zero, LinearMap.zero_apply]

end D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Regularity
