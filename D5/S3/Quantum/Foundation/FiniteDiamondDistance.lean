/- GID: D5/S3/Quantum/Foundation/FiniteDiamondDistance
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FiniteDiamondDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reference-amplified finite channel action and unhalved stabilized trace distance. -/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import Mathlib.Data.Matrix.Composition
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v

namespace D5.S3.Quantum.Foundation.FiniteDiamondDistance

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open Matrix Module
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Kronecker

private def blockEquiv (r a : Type*) [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a] :
    CStarMatrix r r (CStarMatrix a a ℂ) ≃⋆ₐ[ℂ]
      CStarMatrix (r × a) (r × a) ℂ :=
  StarAlgEquiv.ofAlgEquiv
    ((CStarMatrix.ofMatrixStarAlgEquiv (n := r)).symm.toAlgEquiv.trans
      ((Matrix.compAlgEquiv r a ℂ ℂ).trans
        (CStarMatrix.ofMatrixStarAlgEquiv (n := r × a)).toAlgEquiv))
    (by
      intro X
      ext ⟨i, u⟩ ⟨j, v⟩
      change (star X) i j u v = star (X j i v u)
      rw [CStarMatrix.star_apply, CStarMatrix.star_apply])

/-- The linear action on the input factor, with the finite reference first. -/
def referenceLinear {r a b : Type*}
    [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (channel : QuantumChannel a b) :
    CStarMatrix (r × a) (r × a) ℂ →ₗ[ℂ]
      CStarMatrix (r × b) (r × b) ℂ :=
  (blockEquiv r b).toAlgEquiv.toLinearMap.comp
    ((CStarMatrix.mapₗ channel.toCompletelyPositiveMap.toLinearMap).comp
      (blockEquiv r a).symm.toAlgEquiv.toLinearMap)

/-- Apply a channel on the input factor while leaving an arbitrary finite
reference factor untouched. The product index is reference first. -/
def referenceAction {r a b : Type*}
    [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (channel : QuantumChannel a b)
    (X : CStarMatrix (r × a) (r × a) ℂ) :
    CStarMatrix (r × b) (r × b) ℂ :=
  referenceLinear channel X

/-- Complete positivity and trace preservation make the action on the input
factor a density-state transformation for every finite reference factor. -/
def referenceState {r a b : Type*}
    [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (channel : QuantumChannel a b)
    (rho : DensityState (r × a)) : DensityState (r × b) := by
  let Y := (blockEquiv r a).symm rho.1
  have hY : 0 ≤ Y := map_nonneg (blockEquiv r a).symm rho.2.1
  have hPositive : 0 ≤ referenceAction channel rho.1 := by
    change 0 ≤ blockEquiv r b (Y.map channel.toCompletelyPositiveMap)
    exact map_nonneg (blockEquiv r b)
      (CompletelyPositiveMap.map_cstarMatrix_nonneg channel.toCompletelyPositiveMap Y hY)
  have hTrace (X : CStarMatrix (r × a) (r × a) ℂ) :
      Matrix.trace (referenceAction channel X) = Matrix.trace X := by
    calc
      Matrix.trace (referenceAction channel X) =
          ∑ i : r, Matrix.trace (channel.toCompletelyPositiveMap
            (CStarMatrix.ofMatrix fun u v => X (i, u) (i, v))) := by
        change (∑ p : r × b, (referenceAction channel X) p p) =
          ∑ i : r, ∑ u : b, channel.toCompletelyPositiveMap
            (CStarMatrix.ofMatrix fun x y => X (i, x) (i, y)) u u
        rw [Fintype.sum_prod_type]
        change (∑ i : r, ∑ u : b, channel.toCompletelyPositiveMap
            (CStarMatrix.ofMatrix fun x y => X (i, x) (i, y)) u u) =
          ∑ i : r, ∑ u : b, channel.toCompletelyPositiveMap
            (CStarMatrix.ofMatrix fun x y => X (i, x) (i, y)) u u
        rfl
      _ = ∑ i : r, Matrix.trace
          (CStarMatrix.ofMatrix fun u v => X (i, u) (i, v)) := by
        simp only [channel.trace_preserving]
      _ = Matrix.trace X := by
        change (∑ i : r, ∑ u : a, X (i, u) (i, u)) =
          ∑ p : r × a, X p p
        rw [Fintype.sum_prod_type]
  exact ⟨referenceAction channel rho.1, hPositive,
    (hTrace rho.1).trans rho.2.2⟩

/-- The unhalved trace-norm error for one reference system and one joint input
state. The two channels have the same input and output spaces. -/
def referenceError {r a b : Type*}
    [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (first second : QuantumChannel a b)
    (rho : DensityState (r × a)) : ℝ :=
  traceNorm (CStarMatrix.ofMatrix.symm (referenceState first rho).1 -
    CStarMatrix.ofMatrix.symm (referenceState second rho).1)

/-- A rank-one density matrix is pure. -/
def IsPure {q : Type*} [Fintype q] [DecidableEq q]
    (rho : DensityState q) : Prop :=
  ∃ v : q → ℂ,
    rho.1 = CStarMatrix.ofMatrix (Matrix.vecMulVec v (star v))

/-- A unit vector gives a canonical pure density state. -/
def pureState {q : Type*} [Fintype q] [DecidableEq q]
    (v : q → ℂ) (hv : star v ⬝ᵥ v = 1) : DensityState q :=
  ⟨CStarMatrix.ofMatrix (Matrix.vecMulVec v (star v)),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      (Matrix.posSemidef_vecMulVec_self_star v).nonneg,
    by
      change Matrix.trace (Matrix.vecMulVec v (star v)) = 1
      rw [Matrix.trace_vecMulVec, dotProduct_comm]
      exact hv⟩
/-- Unhalved stabilized channel distance, with every finite reference dimension
represented by `Fin n`. The zero term covers empty input spaces, which admit no
density state. -/
def diamondDistance {a b : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (first second : QuantumChannel a b) : ℝ :=
  sSup ({0} ∪ {x : ℝ | ∃ n : ℕ, ∃ rho : DensityState (Fin n × a),
    x = referenceError first second rho})

/-- Pure joint inputs with reference dimension equal to the input dimension suffice. -/
theorem result {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (first second : QuantumChannel a b) :
    (∀ {R : Type v} [Fintype R] [DecidableEq R] (rho : DensityState (R × a)),
      ∃ tau : DensityState (R × a),
        IsPure tau ∧ referenceError first second rho ≤ referenceError first second tau) ∧
    (∀ {R : Type v} [Fintype R] [DecidableEq R] (rho : DensityState (R × a)),
      ∃ tau : DensityState (Fin (Fintype.card a) × a),
        IsPure tau ∧ referenceError first second rho ≤ referenceError first second tau) ∧
    diamondDistance first second =
      sSup ({0} ∪ {x : ℝ | ∃ tau : DensityState (Fin (Fintype.card a) × a),
        IsPure tau ∧ x = referenceError first second tau}) := by
  classical
  have hMixed {R : Type v} [Fintype R] [DecidableEq R] (rho : DensityState (R × a)) :
      ∃ tau : DensityState (R × a),
        IsPure tau ∧ referenceError first second rho ≤ referenceError first second tau := by
    classical
    let q := R × a
    let rhoMatrix : Matrix q q ℂ := CStarMatrix.ofMatrix.symm rho.1
    have hM : rhoMatrix.PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1)
    let hH := hM.isHermitian
    let p : q → ℝ := hH.eigenvalues
    let v : q → q → ℂ := fun i => ⇑(hH.eigenvectorBasis i)
    have hv (i : q) : star (v i) ⬝ᵥ v i = 1 := by
      change star (⇑(hH.eigenvectorBasis i)) ⬝ᵥ ⇑(hH.eigenvectorBasis i) = 1
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
        inner_self_eq_norm_sq_to_K,
        hH.eigenvectorBasis.orthonormal.1 i]
      norm_num
    let psi : q → DensityState q := fun i => pureState (v i) (hv i)
    have hp (i : q) : 0 ≤ p i := hM.eigenvalues_nonneg i
    have hsumC : (∑ i : q, (p i : ℂ)) = 1 := by
      calc
        (∑ i : q, (p i : ℂ)) = rhoMatrix.trace := hH.trace_eq_sum_eigenvalues.symm
        _ = Matrix.trace rho.1 := rfl
        _ = 1 := rho.2.2
    have hsum : (∑ i : q, p i) = 1 := by
      exact_mod_cast hsumC
    have hnonempty : (Finset.univ : Finset q).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      simp [h] at hsum
    have hdecomp : rho.1 = ∑ i : q, (p i : ℂ) • (psi i).1 := by
      apply CStarMatrix.ext
      intro j k
      have hentry : rhoMatrix j k = ∑ i : q, (p i : ℂ) * (v i j * star (v i k)) := by
        rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro i _
        simp [p, v, Matrix.mul_diagonal,
          mul_assoc, mul_left_comm, mul_comm]
      calc
        rho.1 j k = rhoMatrix j k := rfl
        _ = ∑ i : q, (p i : ℂ) * (v i j * star (v i k)) := hentry
        _ = (∑ i : q, (p i : ℂ) • (psi i).1) j k := by
          change (∑ i : q, (p i : ℂ) * (v i j * star (v i k))) =
            (∑ i : q, (p i : ℂ) • Matrix.vecMulVec (v i) (star (v i))) j k
          simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
            Pi.star_apply]
    let L : CStarMatrix q q ℂ →ₗ[ℂ] CStarMatrix (R × (b)) (R × (b)) ℂ :=
      referenceLinear first - referenceLinear second
    have hL : L rho.1 = ∑ i : q, (p i : ℂ) • L (psi i).1 := by
      rw [hdecomp, map_sum]
      simp only [map_smul]
    have hnorm (tau : DensityState q) :
        referenceError first second tau = traceNorm (L tau.1) := rfl
    obtain ⟨U, hU⟩ := (traceNorm_eq_max_re_tr_U (L rho.1)).1
    have hupper : traceNorm (L rho.1) ≤
        ∑ i : q, p i * traceNorm (L (psi i).1) := by
      rw [← hU, hL]
      change Complex.re (Matrix.trace
        (U.val * (∑ i : q, (p i : ℂ) •
          CStarMatrix.ofMatrix.symm (L (psi i).1)))) ≤
        ∑ i : q, p i * traceNorm (L (psi i).1)
      simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum,
        Matrix.mul_smul, Matrix.trace_smul]
      have hre (i : q) :
          ((p i : ℂ) * Matrix.trace
            (U.val * CStarMatrix.ofMatrix.symm (L (psi i).1))).re =
            p i * (Matrix.trace
              (U.val * CStarMatrix.ofMatrix.symm (L (psi i).1))).re := by simp
      apply Finset.sum_le_sum
      intro i _
      change ((p i : ℂ) * Matrix.trace
        (U.val * CStarMatrix.ofMatrix.symm (L (psi i).1))).re ≤
          p i * traceNorm (L (psi i).1)
      rw [hre]
      exact mul_le_mul_of_nonneg_left
        ((traceNorm_eq_max_re_tr_U (L (psi i).1)).2 ⟨U, rfl⟩) (hp i)
    obtain ⟨i, -, hi⟩ :=
      Finset.exists_max_image (Finset.univ : Finset q)
        (fun i => traceNorm (L (psi i).1)) hnonempty
    refine ⟨psi i, ⟨v i, rfl⟩, ?_⟩
    rw [hnorm, hnorm]
    refine hupper.trans ?_
    calc
      (∑ j : q, p j * traceNorm (L (psi j).1)) ≤
          ∑ j : q, p j * traceNorm (L (psi i).1) := by
        exact Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ j)) (hp j))
      _ = traceNorm (L (psi i).1) := by
        rw [← Finset.sum_mul, hsum, one_mul]

  have hFactor {R : Type v} {a : Type u} [Fintype R] [DecidableEq R] [Fintype a] [DecidableEq a]
      (A : Matrix R a ℂ) :
      ∃ (r : ℕ) (_ : r ≤ Fintype.card a)
        (V : Matrix R (Fin r) ℂ) (U : Matrix (Fin r) a ℂ),
        Vᴴ * V = 1 ∧ V * U = A := by
    classical
    let L := Matrix.toEuclideanLin A
    let r := finrank ℂ L.range
    let basis := stdOrthonormalBasis ℂ L.range
    let col (j : a) : L.range :=
      ⟨L (EuclideanSpace.single j 1), ⟨EuclideanSpace.single j 1, rfl⟩⟩
    have hcol (j : a) (x : R) : (col j : EuclideanSpace ℂ R) x = A x j := by
      simp [col, L, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
        EuclideanSpace.single_apply]
    let V : Matrix R (Fin r) ℂ := fun x i => (basis i : EuclideanSpace ℂ R) x
    let U : Matrix (Fin r) a ℂ := fun i j => basis.repr (col j) i
    have hortho : Orthonormal ℂ (fun i : Fin r => (basis i : EuclideanSpace ℂ R)) :=
      basis.orthonormal.comp_linearIsometry L.range.subtypeₗᵢ
    have hV : Vᴴ * V = 1 := by
      ext i j
      change (∑ x : R, star (V x i) * V x j) = if i = j then 1 else 0
      have h := orthonormal_iff_ite.mp hortho i j
      simp only [PiLp.inner_apply, RCLike.inner_apply] at h
      change (∑ x : R, V x j * star (V x i)) = if i = j then 1 else 0 at h
      calc
        _ = ∑ x : R, V x j * star (V x i) :=
          Finset.sum_congr rfl (fun x _ => mul_comm _ _)
        _ = _ := h
    have hVU : V * U = A := by
      ext x j
      have h := congrArg (fun z : L.range => (z : EuclideanSpace ℂ R) x)
        (basis.sum_repr (col j))
      simp only [Submodule.coe_sum, Submodule.coe_smul, WithLp.ofLp_sum, Finset.sum_apply,
        PiLp.smul_apply, smul_eq_mul] at h
      change (∑ i : Fin r, U i j * V x i) = (col j : EuclideanSpace ℂ R) x at h
      change (∑ i : Fin r, V x i * U i j) = A x j
      calc
        _ = ∑ i : Fin r, U i j * V x i :=
          Finset.sum_congr rfl (fun i _ => mul_comm _ _)
        _ = _ := h.trans (hcol j x)
    refine ⟨r, ?_, V, U, hV, hVU⟩
    simpa [r] using L.finrank_range_le

  have hTensor {R : Type v} {a : Type u} {S : Type} [Fintype R] [DecidableEq R]
      [Fintype S] [DecidableEq S] [Fintype a] [DecidableEq a]
      (V : Matrix R S ℂ) (hV : Vᴴ * V = 1) :
      (V ⊗ₖ (1 : Matrix a a ℂ))ᴴ * (V ⊗ₖ (1 : Matrix a a ℂ)) = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hV]
    simp

  have hNorm {R : Type (max u v)} {S : Type u} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
      (V : Matrix R S ℂ) (hV : Vᴴ * V = 1) (v : S → ℂ) :
      star (V *ᵥ v) ⬝ᵥ (V *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hV,
      Matrix.vecMul_one]

  have hEmbedding (r k : ℕ) (hr : r ≤ k) :
      let E : Matrix (Fin k) (Fin r) ℂ :=
        fun x i => if x = Fin.castLE hr i then 1 else 0
      Eᴴ * E = 1 := by
    classical
    dsimp only
    ext i j
    change (∑ x : Fin k, star (if x = Fin.castLE hr i then (1 : ℂ) else 0) *
      (if x = Fin.castLE hr j then 1 else 0)) = if i = j then 1 else 0
    simp [Fin.castLE_injective hr |>.eq_iff, eq_comm]

  have hVector {R : Type v} {a : Type u} {S : Type} [Fintype R] [DecidableEq R]
      [Fintype S] [DecidableEq S] [Fintype a] [DecidableEq a]
      (V : Matrix R S ℂ) (U : Matrix S a ℂ) :
      (V ⊗ₖ (1 : Matrix a a ℂ)) *ᵥ (fun p : S × a => U p.1 p.2) =
        fun p : R × a => (V * U) p.1 p.2 := by
    classical
    ext ⟨i, j⟩
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.mul_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply]

  have hOuter {R : Type (max u v)} {S : Type u} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
      (V : Matrix R S ℂ) (u : S → ℂ) :
      Matrix.vecMulVec (V *ᵥ u) (star (V *ᵥ u)) =
        V * Matrix.vecMulVec u (star u) * Vᴴ := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]
  have hCov {R : Type v} {a b : Type u} {S : Type} [Fintype R] [DecidableEq R]
      [Fintype S] [DecidableEq S] [Fintype a] [DecidableEq a]
      [Fintype b] [DecidableEq b]
      (channel : QuantumChannel a b) (V : Matrix R S ℂ)
      (X : Matrix (S × a) (S × a) ℂ) :
      referenceLinear channel (CStarMatrix.ofMatrix
        ((V ⊗ₖ (1 : Matrix a a ℂ)) * X * (V ⊗ₖ (1 : Matrix a a ℂ))ᴴ)) =
      CStarMatrix.ofMatrix ((V ⊗ₖ (1 : Matrix b b ℂ)) *
        CStarMatrix.ofMatrix.symm (referenceLinear channel (CStarMatrix.ofMatrix X)) *
        (V ⊗ₖ (1 : Matrix b b ℂ))ᴴ) := by
    classical
    have hBlock {q : Type u} [Fintype q] [DecidableEq q]
        (Y : Matrix (S × q) (S × q) ℂ) (i j : R) (u v : q) :
        ((V ⊗ₖ (1 : Matrix q q ℂ)) * Y * (V ⊗ₖ (1 : Matrix q q ℂ))ᴴ)
          (i, u) (j, v) =
        ∑ k, ∑ l, (V i k * star (V j l)) * Y (k, u) (l, v) := by
      simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
        Matrix.kroneckerMap_apply, Matrix.one_apply, Finset.sum_mul, Finset.mul_sum,
        apply_ite, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
        star_zero, star_one, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
        if_true]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    have hBlockMatrix (i j : R) :
        (CStarMatrix.ofMatrix fun u v =>
          ((V ⊗ₖ (1 : Matrix a a ℂ)) * X * (V ⊗ₖ (1 : Matrix a a ℂ))ᴴ)
            (i, u) (j, v)) =
        ∑ k, ∑ l, (V i k * star (V j l)) •
          CStarMatrix.ofMatrix (fun u v => X (k, u) (l, v)) := by
      ext u v
      have hSumEval (f : S → CStarMatrix a a ℂ) :
          (∑ k, f k) u v = ∑ k, f k u v :=
        Matrix.sum_apply u v Finset.univ f
      simp_rw [hSumEval]
      simp only [CStarMatrix.smul_apply, smul_eq_mul, CStarMatrix.ofMatrix_apply]
      exact hBlock X i j u v
    ext ⟨i, u⟩ ⟨j, v⟩
    change channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix fun x y =>
      ((V ⊗ₖ (1 : Matrix a a ℂ)) * X * (V ⊗ₖ (1 : Matrix a a ℂ))ᴴ)
        (i, x) (j, y)) u v = _
    rw [hBlockMatrix]
    simp only [map_sum, map_smul]
    change (∑ k, ∑ l, (V i k * star (V j l)) •
      CStarMatrix.ofMatrix.symm (channel.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix fun x y => X (k, x) (l, y))) : Matrix b b ℂ) u v = _
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    change _ = ((V ⊗ₖ (1 : Matrix b b ℂ)) *
      CStarMatrix.ofMatrix.symm (referenceLinear channel (CStarMatrix.ofMatrix X)) *
      (V ⊗ₖ (1 : Matrix b b ℂ))ᴴ) (i, u) (j, v)
    rw [hBlock]
    rfl
  have hIso {M : Type (max u v)} {N : Type u} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
      (V : Matrix M N ℂ) (hV : Vᴴ * V = 1) (X : Matrix N N ℂ) :
      traceNorm (V * X * Vᴴ) = traceNorm X := by
    let P := CFC.sqrt (Xᴴ * X)
    have hXX : 0 ≤ Xᴴ * X := (Matrix.posSemidef_conjTranspose_mul_self X).nonneg
    have hgram : (V * X * Vᴴ)ᴴ * (V * X * Vᴴ) = V * (Xᴴ * X) * Vᴴ := by
      calc
        _ = V * Xᴴ * (Vᴴ * V) * X * Vᴴ := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            Matrix.mul_assoc]
        _ = _ := by rw [hV]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    have hP : 0 ≤ P := CFC.sqrt_nonneg _
    have hsquare : (V * P * Vᴴ) * (V * P * Vᴴ) = V * (Xᴴ * X) * Vᴴ := by
      calc
        _ = V * P * (Vᴴ * V) * P * Vᴴ := by simp only [Matrix.mul_assoc]
        _ = V * (P * P) * Vᴴ := by rw [hV]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = _ := by rw [show P * P = Xᴴ * X from CFC.sqrt_mul_sqrt_self _ hXX]
    have hpositive : 0 ≤ V * P * Vᴴ :=
      ((Matrix.nonneg_iff_posSemidef.mp hP).mul_mul_conjTranspose_same V).nonneg
    have hsqrt : CFC.sqrt (V * (Xᴴ * X) * Vᴴ) = V * P * Vᴴ :=
      CFC.sqrt_unique hsquare hpositive
    change (CFC.sqrt ((V * X * Vᴴ)ᴴ * (V * X * Vᴴ))).trace.re =
      (CFC.sqrt (Xᴴ * X)).trace.re
    rw [hgram, hsqrt, Matrix.trace_mul_cycle, hV, Matrix.one_mul]
  have hError {S : Type} {T : Type v} [Fintype S] [DecidableEq S]
      [Fintype T] [DecidableEq T] (V : Matrix T S ℂ) (hV : Vᴴ * V = 1)
      (w : S × a → ℂ) (hw : star w ⬝ᵥ w = 1) :
      referenceError first second
        (pureState ((V ⊗ₖ (1 : Matrix a a ℂ)) *ᵥ w)
          ((hNorm _ (hTensor V hV) w).trans hw)) =
      referenceError first second (pureState w hw) := by
    let B := V ⊗ₖ (1 : Matrix b b ℂ)
    have hAction (C : QuantumChannel a b) :
        CStarMatrix.ofMatrix.symm (referenceLinear C
          (CStarMatrix.ofMatrix (Matrix.vecMulVec
            ((V ⊗ₖ (1 : Matrix a a ℂ)) *ᵥ w)
            (star ((V ⊗ₖ (1 : Matrix a a ℂ)) *ᵥ w))))) =
        B * CStarMatrix.ofMatrix.symm (referenceLinear C
          (CStarMatrix.ofMatrix (Matrix.vecMulVec w (star w)))) * Bᴴ := by
      rw [hOuter]
      exact congrArg CStarMatrix.ofMatrix.symm (hCov C V (Matrix.vecMulVec w (star w)))
    change traceNorm (CStarMatrix.ofMatrix.symm (referenceLinear first
      (CStarMatrix.ofMatrix (Matrix.vecMulVec _ (star _)))) -
      CStarMatrix.ofMatrix.symm (referenceLinear second
        (CStarMatrix.ofMatrix (Matrix.vecMulVec _ (star _))))) = _
    rw [hAction first, hAction second, ← Matrix.sub_mul, ← Matrix.mul_sub]
    exact hIso B (hTensor V hV) _
  have hTensor0 {R S : Type} {a : Type u} [Fintype R] [DecidableEq R]
      [Fintype S] [DecidableEq S] [Fintype a] [DecidableEq a]
      (V : Matrix R S ℂ) (hV : Vᴴ * V = 1) :
      (V ⊗ₖ (1 : Matrix a a ℂ))ᴴ * (V ⊗ₖ (1 : Matrix a a ℂ)) = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hV]
    simp

  have hCov0 {R S : Type} {a b : Type u} [Fintype R] [DecidableEq R]
      [Fintype S] [DecidableEq S] [Fintype a] [DecidableEq a]
      [Fintype b] [DecidableEq b]
      (channel : QuantumChannel a b) (V : Matrix R S ℂ)
      (X : Matrix (S × a) (S × a) ℂ) :
      referenceLinear channel (CStarMatrix.ofMatrix
        ((V ⊗ₖ (1 : Matrix a a ℂ)) * X * (V ⊗ₖ (1 : Matrix a a ℂ))ᴴ)) =
      CStarMatrix.ofMatrix ((V ⊗ₖ (1 : Matrix b b ℂ)) *
        CStarMatrix.ofMatrix.symm (referenceLinear channel (CStarMatrix.ofMatrix X)) *
        (V ⊗ₖ (1 : Matrix b b ℂ))ᴴ) := by
    classical
    have hBlock {q : Type u} [Fintype q] [DecidableEq q]
        (Y : Matrix (S × q) (S × q) ℂ) (i j : R) (u v : q) :
        ((V ⊗ₖ (1 : Matrix q q ℂ)) * Y * (V ⊗ₖ (1 : Matrix q q ℂ))ᴴ)
          (i, u) (j, v) =
        ∑ k, ∑ l, (V i k * star (V j l)) * Y (k, u) (l, v) := by
      simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
        Matrix.kroneckerMap_apply, Matrix.one_apply, Finset.sum_mul, Finset.mul_sum,
        apply_ite, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
        star_zero, star_one, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
        if_true]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    have hBlockMatrix (i j : R) :
        (CStarMatrix.ofMatrix fun u v =>
          ((V ⊗ₖ (1 : Matrix a a ℂ)) * X * (V ⊗ₖ (1 : Matrix a a ℂ))ᴴ)
            (i, u) (j, v)) =
        ∑ k, ∑ l, (V i k * star (V j l)) •
          CStarMatrix.ofMatrix (fun u v => X (k, u) (l, v)) := by
      ext u v
      have hSumEval (f : S → CStarMatrix a a ℂ) :
          (∑ k, f k) u v = ∑ k, f k u v :=
        Matrix.sum_apply u v Finset.univ f
      simp_rw [hSumEval]
      simp only [CStarMatrix.smul_apply, smul_eq_mul, CStarMatrix.ofMatrix_apply]
      exact hBlock X i j u v
    ext ⟨i, u⟩ ⟨j, v⟩
    change channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix fun x y =>
      ((V ⊗ₖ (1 : Matrix a a ℂ)) * X * (V ⊗ₖ (1 : Matrix a a ℂ))ᴴ)
        (i, x) (j, y)) u v = _
    rw [hBlockMatrix]
    simp only [map_sum, map_smul]
    change (∑ k, ∑ l, (V i k * star (V j l)) •
      CStarMatrix.ofMatrix.symm (channel.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix fun x y => X (k, x) (l, y))) : Matrix b b ℂ) u v = _
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    change _ = ((V ⊗ₖ (1 : Matrix b b ℂ)) *
      CStarMatrix.ofMatrix.symm (referenceLinear channel (CStarMatrix.ofMatrix X)) *
      (V ⊗ₖ (1 : Matrix b b ℂ))ᴴ) (i, u) (j, v)
    rw [hBlock]
    rfl
  have hNorm0 {R S : Type u} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
      (V : Matrix R S ℂ) (hV : Vᴴ * V = 1) (v : S → ℂ) :
      star (V *ᵥ v) ⬝ᵥ (V *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hV,
      Matrix.vecMul_one]

  have hOuter0 {R S : Type u} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
      (V : Matrix R S ℂ) (u : S → ℂ) :
      Matrix.vecMulVec (V *ᵥ u) (star (V *ᵥ u)) =
        V * Matrix.vecMulVec u (star u) * Vᴴ := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]
  have hIso0 {M N : Type u} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
      (V : Matrix M N ℂ) (hV : Vᴴ * V = 1) (X : Matrix N N ℂ) :
      traceNorm (V * X * Vᴴ) = traceNorm X := by
    let P := CFC.sqrt (Xᴴ * X)
    have hXX : 0 ≤ Xᴴ * X := (Matrix.posSemidef_conjTranspose_mul_self X).nonneg
    have hgram : (V * X * Vᴴ)ᴴ * (V * X * Vᴴ) = V * (Xᴴ * X) * Vᴴ := by
      calc
        _ = V * Xᴴ * (Vᴴ * V) * X * Vᴴ := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            Matrix.mul_assoc]
        _ = _ := by rw [hV]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    have hP : 0 ≤ P := CFC.sqrt_nonneg _
    have hsquare : (V * P * Vᴴ) * (V * P * Vᴴ) = V * (Xᴴ * X) * Vᴴ := by
      calc
        _ = V * P * (Vᴴ * V) * P * Vᴴ := by simp only [Matrix.mul_assoc]
        _ = V * (P * P) * Vᴴ := by rw [hV]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = _ := by rw [show P * P = Xᴴ * X from CFC.sqrt_mul_sqrt_self _ hXX]
    have hpositive : 0 ≤ V * P * Vᴴ :=
      ((Matrix.nonneg_iff_posSemidef.mp hP).mul_mul_conjTranspose_same V).nonneg
    have hsqrt : CFC.sqrt (V * (Xᴴ * X) * Vᴴ) = V * P * Vᴴ :=
      CFC.sqrt_unique hsquare hpositive
    change (CFC.sqrt ((V * X * Vᴴ)ᴴ * (V * X * Vᴴ))).trace.re =
      (CFC.sqrt (Xᴴ * X)).trace.re
    rw [hgram, hsqrt, Matrix.trace_mul_cycle, hV, Matrix.one_mul]
  have hError0 {S T : Type} [Fintype S] [DecidableEq S]
      [Fintype T] [DecidableEq T] (V : Matrix T S ℂ) (hV : Vᴴ * V = 1)
      (w : S × a → ℂ) (hw : star w ⬝ᵥ w = 1) :
      referenceError first second
        (pureState ((V ⊗ₖ (1 : Matrix a a ℂ)) *ᵥ w)
          ((hNorm0 _ (hTensor0 V hV) w).trans hw)) =
      referenceError first second (pureState w hw) := by
    let B := V ⊗ₖ (1 : Matrix b b ℂ)
    have hAction (C : QuantumChannel a b) :
        CStarMatrix.ofMatrix.symm (referenceLinear C
          (CStarMatrix.ofMatrix (Matrix.vecMulVec
            ((V ⊗ₖ (1 : Matrix a a ℂ)) *ᵥ w)
            (star ((V ⊗ₖ (1 : Matrix a a ℂ)) *ᵥ w))))) =
        B * CStarMatrix.ofMatrix.symm (referenceLinear C
          (CStarMatrix.ofMatrix (Matrix.vecMulVec w (star w)))) * Bᴴ := by
      rw [hOuter0]
      exact congrArg CStarMatrix.ofMatrix.symm (hCov0 C V (Matrix.vecMulVec w (star w)))
    change traceNorm (CStarMatrix.ofMatrix.symm (referenceLinear first
      (CStarMatrix.ofMatrix (Matrix.vecMulVec _ (star _)))) -
      CStarMatrix.ofMatrix.symm (referenceLinear second
        (CStarMatrix.ofMatrix (Matrix.vecMulVec _ (star _))))) = _
    rw [hAction first, hAction second, ← Matrix.sub_mul, ← Matrix.mul_sub]
    exact hIso0 B (hTensor0 V hV) _

  have hPure {R : Type v} [Fintype R] [DecidableEq R] (rho : DensityState (R × a))
      (hpure : IsPure rho) :
      ∃ tau : DensityState (Fin (Fintype.card a) × a),
        IsPure tau ∧ referenceError first second rho = referenceError first second tau := by
    classical
    obtain ⟨w, hw⟩ := hpure
    have hwNorm : star w ⬝ᵥ w = 1 := by
      have h := rho.2.2
      rw [hw] at h
      change Matrix.trace (Matrix.vecMulVec w (star w)) = 1 at h
      rw [Matrix.trace_vecMulVec, dotProduct_comm] at h
      exact h
    let A : Matrix R a ℂ := fun x j => w (x, j)
    obtain ⟨r, hr, V, U, hV, hVU⟩ := hFactor A
    let u : Fin r × a → ℂ := fun p => U p.1 p.2
    let W := V ⊗ₖ (1 : Matrix a a ℂ)
    have hWu : W *ᵥ u = w := by
      dsimp only [W, u]
      rw [hVector V U, hVU]
    have hu : star u ⬝ᵥ u = 1 := by
      have h := hNorm W (hTensor V hV) u
      rw [hWu] at h
      exact h.symm.trans hwNorm
    let E : Matrix (Fin (Fintype.card a)) (Fin r) ℂ :=
      fun x i => if x = Fin.castLE hr i then 1 else 0
    have hE : Eᴴ * E = 1 := hEmbedding r (Fintype.card a) hr
    let fixed := (E ⊗ₖ (1 : Matrix a a ℂ)) *ᵥ u
    have hFixed : star fixed ⬝ᵥ fixed = 1 :=
      (hNorm0 _ (hTensor0 E hE) u).trans hu
    let tau := pureState fixed hFixed
    refine ⟨tau, ⟨fixed, rfl⟩, ?_⟩
    have hRho : rho = pureState (W *ᵥ u) ((hNorm W (hTensor V hV) u).trans hu) := by
      apply Subtype.ext
      change rho.1 = CStarMatrix.ofMatrix (Matrix.vecMulVec (W *ᵥ u) (star (W *ᵥ u)))
      rw [hWu]
      exact hw
    rw [hRho]
    exact (hError V hV u hu).trans (hError0 E hE u hu).symm

  have hDom {R : Type v} [Fintype R] [DecidableEq R] (rho : DensityState (R × a)) :
      ∃ tau : DensityState (Fin (Fintype.card a) × a),
        IsPure tau ∧ referenceError first second rho ≤ referenceError first second tau := by
    obtain ⟨sigma, hSigma, hLe⟩ := hMixed rho
    obtain ⟨tau, hTau, hEq⟩ := hPure sigma hSigma
    exact ⟨tau, hTau, hLe.trans_eq hEq⟩
  have hFiniteDom (n : ℕ) (rho : DensityState (Fin n × a)) :
      ∃ tau : DensityState (Fin (Fintype.card a) × a),
        IsPure tau ∧ referenceError first second rho ≤ referenceError first second tau := by
    let V : Matrix (ULift.{v} (Fin n)) (Fin n) ℂ :=
      fun x i => if x.down = i then 1 else 0
    have hV : Vᴴ * V = 1 := by
      ext i j
      change (∑ x : ULift.{v} (Fin n),
        star (if x.down = i then (1 : ℂ) else 0) *
          (if x.down = j then 1 else 0)) = if i = j then 1 else 0
      calc
        _ = ∑ x : Fin n, star (if x = i then (1 : ℂ) else 0) *
            (if x = j then 1 else 0) :=
          (Equiv.ulift : ULift.{v} (Fin n) ≃ Fin n).sum_comp
            (fun x => star (if x = i then (1 : ℂ) else 0) *
              (if x = j then 1 else 0))
        _ = _ := by simp [eq_comm]
    let A := V ⊗ₖ (1 : Matrix a a ℂ)
    let B := V ⊗ₖ (1 : Matrix b b ℂ)
    let X := CStarMatrix.ofMatrix.symm rho.1
    have hA : Aᴴ * A = 1 := hTensor V hV
    have hB : Bᴴ * B = 1 := hTensor V hV
    have hX : X.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1)
    let lifted : DensityState (ULift.{v} (Fin n) × a) :=
      ⟨CStarMatrix.ofMatrix (A * X * Aᴴ),
        map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
          (hX.mul_mul_conjTranspose_same A).nonneg,
        by
          change Matrix.trace (A * X * Aᴴ) = 1
          rw [Matrix.trace_mul_cycle, hA, Matrix.one_mul]
          exact rho.2.2⟩
    have hAction (C : QuantumChannel a b) :
        CStarMatrix.ofMatrix.symm (referenceLinear C lifted.1) =
        B * CStarMatrix.ofMatrix.symm (referenceLinear C rho.1) * Bᴴ :=
      congrArg CStarMatrix.ofMatrix.symm (hCov C V X)
    have hErrorLift : referenceError first second lifted =
        referenceError first second rho := by
      change traceNorm (CStarMatrix.ofMatrix.symm (referenceLinear first lifted.1) -
        CStarMatrix.ofMatrix.symm (referenceLinear second lifted.1)) = _
      rw [hAction first, hAction second, ← Matrix.sub_mul, ← Matrix.mul_sub]
      exact hIso B hB _
    obtain ⟨tau, hTau, hLe⟩ := hDom lifted
    exact ⟨tau, hTau, hErrorLift.symm.le.trans hLe⟩
  refine ⟨hMixed, hDom, ?_⟩
  change sSup ({0} ∪ {x : ℝ | ∃ n : ℕ, ∃ rho : DensityState (Fin n × a),
    x = referenceError first second rho}) = _
  apply csSup_eq_csSup_of_forall_exists_le
  · intro x hx
    rcases hx with hx | ⟨n, rho, rfl⟩
    · exact ⟨x, Or.inl hx, le_rfl⟩
    · obtain ⟨tau, hTau, hLe⟩ := hFiniteDom n rho
      exact ⟨referenceError first second tau, Or.inr ⟨tau, hTau, rfl⟩, hLe⟩
  · intro x hx
    rcases hx with hx | ⟨rho, -, rfl⟩
    · exact ⟨x, Or.inl hx, le_rfl⟩
    · exact ⟨referenceError first second rho,
        Or.inr ⟨Fintype.card a, rho, rfl⟩, le_rfl⟩

end D5.S3.Quantum.Foundation.FiniteDiamondDistance
