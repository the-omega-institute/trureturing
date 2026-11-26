/- GID: D5/S3/Quantum/Divergence/PositiveKrausCompression
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/PositiveKrausCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A positive trace-one replacement preserves the supported Kraus compression bound. -/

import D5.S3.Quantum.Divergence.CanonicalRelativeModularModel
import D5.S3.Quantum.Divergence.UniversalCommonCenter
import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.HilbertOperators.DouglasLemma
import Mathlib.Analysis.InnerProductSpace.Positive
import D5.S3.Quantum.Analysis.TraceClass.Polar
import D5.S3.Quantum.Analysis.TraceClass.Basic
import D5.S3.Quantum.Analysis.TraceClass.Pairing
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

/-! The selected-column estimate supplies a supported rectangular factor.
The singular polar construction replaces its complex trace-one compression
by a positive state while preserving the Gram bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Kronecker
open Matrix

namespace D5.S3.Quantum.Divergence.UniversalPositiveScalarizer

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Divergence.UniversalCommonCenter

universe u

variable {a b : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]

private abbrev matrixCLM {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (M : Matrix m n ℂ) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap

private def padLeft {m p q : Type*} (D : Matrix m p ℂ) : Matrix m (Sum p q) ℂ :=
  fun i j => match j with | Sum.inl p' => D i p' | Sum.inr _ => 0

private def padRight {m p q : Type*} (C : Matrix m q ℂ) : Matrix m (Sum p q) ℂ :=
  fun i j => match j with | Sum.inl _ => 0 | Sum.inr q' => C i q'

private lemma padLeft_mulVec {m p q : Type*} [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (D : Matrix m p ℂ) (z : EuclideanSpace ℂ m) (i : p) :
    ((padLeft (q := q) D).conjTranspose *ᵥ z.ofLp) (Sum.inl (β := q) i) =
      (D.conjTranspose *ᵥ z.ofLp) i := by
  simp [padLeft, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct]

private lemma padRight_mulVec {m p q : Type*} [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (C : Matrix m q ℂ) (z : EuclideanSpace ℂ m) (j : q) :
    ((padRight (p := p) C).conjTranspose *ᵥ z.ofLp) (Sum.inr (α := p) j) =
      (C.conjTranspose *ᵥ z.ofLp) j := by
  simp [padRight, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct]

private lemma padLeft_norm {m p q : Type*} [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (D : Matrix m p ℂ) (z : EuclideanSpace ℂ m) :
    ‖(Matrix.toEuclideanLin (padLeft (q := q) D).conjTranspose) z‖ ^ 2 =
      ‖(Matrix.toEuclideanLin D.conjTranspose) z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  rw [Fintype.sum_sum_type]
  have hz : ∀ j : q, ((padLeft (q := q) D).conjTranspose *ᵥ z.ofLp)
      (Sum.inr (α := p) j) = 0 := by
    intro j
    simp [padLeft, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct]
  simp [padLeft_mulVec, hz]

private lemma padRight_norm {m p q : Type*} [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (C : Matrix m q ℂ) (z : EuclideanSpace ℂ m) :
    ‖(Matrix.toEuclideanLin (padRight (p := p) C).conjTranspose) z‖ ^ 2 =
      ‖(Matrix.toEuclideanLin C.conjTranspose) z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  rw [Fintype.sum_sum_type]
  have hz : ∀ i : p, ((padRight (p := p) C).conjTranspose *ᵥ z.ofLp)
      (Sum.inl (β := q) i) = 0 := by
    intro i
    simp [padRight, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct]
  simp [padRight_mulVec, hz]

private lemma gram_majorization {m p q : Type*} [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (C : Matrix m q ℂ) (D : Matrix m p ℂ) (k : ℝ) (hk : 0 ≤ k)
    (hgram : ((k : ℂ) • (C * Cᴴ) - D * Dᴴ).PosSemidef) :
    ∀ z : EuclideanSpace ℂ m,
      ‖(Matrix.toEuclideanLin Dᴴ) z‖ ≤ Real.sqrt k * ‖(Matrix.toEuclideanLin Cᴴ) z‖ := by
  intro z
  have hp := hgram.dotProduct_mulVec_nonneg z.ofLp
  have hC : star z.ofLp ⬝ᵥ ((C * Cᴴ) *ᵥ z.ofLp) =
      star (Cᴴ *ᵥ z.ofLp) ⬝ᵥ (Cᴴ *ᵥ z.ofLp) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.mulVec_conjTranspose C z.ofLp, star_star]
  have hD : star z.ofLp ⬝ᵥ ((D * Dᴴ) *ᵥ z.ofLp) =
      star (Dᴴ *ᵥ z.ofLp) ⬝ᵥ (Dᴴ *ᵥ z.ofLp) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.mulVec_conjTranspose D z.ofLp, star_star]
  have hp' := (Complex.nonneg_iff.mp hp).1
  have hsq : ‖(Matrix.toEuclideanLin Dᴴ) z‖ ^ 2 ≤
      k * ‖(Matrix.toEuclideanLin Cᴴ) z‖ ^ 2 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
      dotProduct_smul] at hp'
    have hp'' : 0 ≤ k *
        (star z.ofLp ⬝ᵥ ((C * Cᴴ) *ᵥ z.ofLp)).re -
        (star z.ofLp ⬝ᵥ ((D * Dᴴ) *ᵥ z.ofLp)).re := by
      simpa using hp'
    rw [hC, hD] at hp''
    have hnormC : ‖(Matrix.toEuclideanLin Cᴴ) z‖ ^ 2 =
        (star (Cᴴ *ᵥ z.ofLp) ⬝ᵥ (Cᴴ *ᵥ z.ofLp)).re := by
      simp [EuclideanSpace.norm_sq_eq, Matrix.toLpLin_apply, dotProduct,
        Complex.sq_norm, Complex.normSq_apply, Complex.normSq_eq_conj_mul_self]
    have hnormD : ‖(Matrix.toEuclideanLin Dᴴ) z‖ ^ 2 =
        (star (Dᴴ *ᵥ z.ofLp) ⬝ᵥ (Dᴴ *ᵥ z.ofLp)).re := by
      simp [EuclideanSpace.norm_sq_eq, Matrix.toLpLin_apply, dotProduct,
        Complex.sq_norm, Complex.normSq_apply, Complex.normSq_eq_conj_mul_self]
    rw [hnormD, hnormC]
    linarith
  have hsqrt : 0 ≤ Real.sqrt k := Real.sqrt_nonneg _
  have hsqrt2 : (Real.sqrt k) ^ 2 = k := Real.sq_sqrt hk
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hsqrt (norm_nonneg _))).mp
  calc
    ‖(Matrix.toEuclideanLin Dᴴ) z‖ ^ 2 ≤
        k * ‖(Matrix.toEuclideanLin Cᴴ) z‖ ^ 2 := hsq
    _ = (Real.sqrt k * ‖(Matrix.toEuclideanLin Cᴴ) z‖) ^ 2 := by
      rw [mul_pow, hsqrt2]

private lemma matrixCLM_adjoint {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (M : Matrix m n ℂ) :
    (matrixCLM M).adjoint = matrixCLM Mᴴ := by
  unfold matrixCLM
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_toContinuousLinearMap]

private lemma norm_padLeft_eq {m p q : Type*} [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (D : Matrix m p ℂ) (z : EuclideanSpace ℂ m) :
    ‖(Matrix.toEuclideanLin (padLeft (q := q) D).conjTranspose) z‖ =
      ‖(Matrix.toEuclideanLin D.conjTranspose) z‖ := by
  have h := padLeft_norm (q := q) D z
  nlinarith [norm_nonneg ((Matrix.toEuclideanLin (padLeft (q := q) D).conjTranspose) z),
    norm_nonneg ((Matrix.toEuclideanLin D.conjTranspose) z)]

private lemma norm_padRight_eq {m p q : Type*} [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (C : Matrix m q ℂ) (z : EuclideanSpace ℂ m) :
    ‖(Matrix.toEuclideanLin (padRight (p := p) C).conjTranspose) z‖ =
      ‖(Matrix.toEuclideanLin C.conjTranspose) z‖ := by
  have h := padRight_norm (p := p) C z
  nlinarith [norm_nonneg ((Matrix.toEuclideanLin (padRight (p := p) C).conjTranspose) z),
    norm_nonneg ((Matrix.toEuclideanLin C.conjTranspose) z)]

private lemma padded_douglas {m p q : Type*} [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (C : Matrix m q ℂ) (D : Matrix m p ℂ) (k : ℝ) (hk : 0 ≤ k)
    (hgram : ((k : ℂ) • (C * Cᴴ) - D * Dᴴ).PosSemidef) :
    ∃ L : EuclideanSpace ℂ (Sum p q) →L[ℂ] EuclideanSpace ℂ (Sum p q),
      matrixCLM (padLeft (q := q) D) =
        (matrixCLM (padRight (p := p) C)).comp L ∧ ‖L‖ ≤ Real.sqrt k := by
  apply D5.S3.HilbertOperators.DouglasLemma.exists_factorization_of_majorization
    (matrixCLM (padLeft (q := q) D)) (matrixCLM (padRight (p := p) C))
    (Real.sqrt_nonneg k)
  intro z
  rw [matrixCLM_adjoint, matrixCLM_adjoint]
  change ‖Matrix.toEuclideanLin (padLeft (q := q) D)ᴴ z‖ ≤
    Real.sqrt k * ‖Matrix.toEuclideanLin (padRight (p := p) C)ᴴ z‖
  rw [norm_padLeft_eq, norm_padRight_eq]
  exact gram_majorization C D k hk hgram z

private lemma rectangular_douglas {m p q : Type*} [Fintype m] [DecidableEq m]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (C : Matrix m q ℂ) (D : Matrix m p ℂ) (k : ℝ) (hk : 0 ≤ k)
    (hgram : ((k : ℂ) • (C * Cᴴ) - D * Dᴴ).PosSemidef) :
    ∃ T : Matrix q p ℂ, C * T = D ∧
      ∀ z : EuclideanSpace ℂ p, ‖Matrix.toEuclideanLin T z‖ ≤ Real.sqrt k * ‖z‖ := by
  obtain ⟨L, hL, hLn⟩ := padded_douglas C D k hk hgram
  let M : Matrix (Sum p q) (Sum p q) ℂ := Matrix.toEuclideanLin.symm L.toLinearMap
  have hM : Matrix.toEuclideanLin M = L.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply _
  have hLM : padLeft (q := q) D = padRight (p := p) C * M := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul_same, hM]
    exact congrArg ContinuousLinearMap.toLinearMap hL
  let T : Matrix q p ℂ := fun j i => M (Sum.inr j) (Sum.inl i)
  refine ⟨T, ?_, ?_⟩
  · ext i j
    have hij := congrArg (fun A => A i (Sum.inl j)) hLM
    change (∑ x, C i x * T x j) = D i j
    simpa [padLeft, padRight, Matrix.mul_apply, Fintype.sum_sum_type, T] using hij.symm
  · intro z
    let z' : EuclideanSpace ℂ (Sum p q) := WithLp.toLp 2 (Sum.elim z.ofLp (fun _ => 0))
    have hz : ‖z'‖ = ‖z‖ := by
      have hs : ‖z'‖ ^ 2 = ‖z‖ ^ 2 := by
        simp [EuclideanSpace.norm_sq_eq, z', Fintype.sum_sum_type]
      nlinarith [norm_nonneg z', norm_nonneg z]
    have heq : ∀ j : q, (Matrix.toEuclideanLin T z) j = (L z') (Sum.inr j) := by
      intro j
      have hm := congrArg (fun f => (f z') (Sum.inr j)) hM
      change (∑ i, T j i * z.ofLp i) = (L z') (Sum.inr j)
      simpa [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
        T, z', Fintype.sum_sum_type] using hm
    have hpart : ‖Matrix.toEuclideanLin T z‖ ≤ ‖L z'‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
      simp_rw [heq]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact hpart.trans ((L.le_opNorm z').trans (by gcongr; rw [hz]))

private lemma norm_bound_gram {p q : Type*} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q] (T : Matrix q p ℂ) (k : ℝ) (hk : 0 ≤ k)
    (hT : ∀ z : EuclideanSpace ℂ p, ‖Matrix.toEuclideanLin T z‖ ≤ Real.sqrt k * ‖z‖) :
    ((k : ℂ) • (1 : Matrix p p ℂ) - Tᴴ * T).PosSemidef := by
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  refine ⟨Matrix.isSymmetric_toEuclideanLin_iff.mpr ?_, ?_⟩
  · change ((k : ℂ) • (1 : Matrix p p ℂ) - Tᴴ * T)ᴴ = _
    simp
  · intro z
    have hn := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hT z)
    rw [mul_pow, Real.sq_sqrt hk] at hn
    have heq :
        Matrix.toEuclideanLin ((k : ℂ) • (1 : Matrix p p ℂ) - Tᴴ * T) z =
        (k : ℂ) • z - (Matrix.toEuclideanLin T).adjoint (Matrix.toEuclideanLin T z) := by
      rw [map_sub, map_smul, Matrix.toLpLin_mul_same,
        Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      simp [Matrix.toEuclideanLin]
    rw [heq, inner_sub_left, inner_smul_left, LinearMap.adjoint_inner_left]
    simpa [inner_self_eq_norm_sq_to_K, Complex.conj_ofReal,
      Complex.mul_re, ← Complex.ofReal_pow, matrixCLM] using sub_nonneg.mpr hn

abbrev Env (a b : Type*) [Fintype a] [Fintype b] :=
  Fin (Fintype.card b) × Fin (Fintype.card a)

abbrev K (Φ : QuantumChannel a b) : Env a b → Matrix b a ℂ :=
  (actual_kraus_representation Φ).kraus

/-- The actual Stinespring column, with output index first as required by the
canonical Kraus convention. -/
def J (Φ : QuantumChannel a b) : Matrix (b × Env a b) a ℂ :=
  krausColumn (K Φ)

private lemma J_isometry (Φ : QuantumChannel a b) : (J Φ)ᴴ * J Φ = 1 :=
  krausColumn_isometry (K Φ) (actual_kraus_representation Φ).hkraus

/-- The actual output-to-input trace adjoint of the canonical Kraus family. -/
def Phi (Φ : QuantumChannel a b) (Y : Matrix b b ℂ) : Matrix a a ℂ :=
  krausAdjoint (K Φ) Y

/-- The reference-amplified actual adjoint.  This definition is valid for an
empty reference as well as every inhabited finite reference. -/
def PhiR (Φ : QuantumChannel a b) {R : Type u}
    [Fintype R] [DecidableEq R] (Y : Matrix (R × b) (R × b) ℂ) :
    Matrix (R × a) (R × a) ℂ :=
  fun (r,x) (s,y) => Phi Φ (fun u v => Y (r,u) (s,v)) x y

def pi (Y : Matrix b b ℂ) :
    Matrix (b × Env a b) (b × Env a b) ℂ :=
  fun (u,c) (v,d) => if c = d then Y u v else 0

def e (Φ : QuantumChannel a b) :
    Matrix (b × Env a b) (b × Env a b) ℂ :=
  1 - J Φ * (J Φ)ᴴ

private lemma pi_eq_kronecker (Y : Matrix b b ℂ) :
    pi (a := a) Y = Matrix.kronecker Y (1 : Matrix (Env a b) (Env a b) ℂ) := by
  ext ⟨u,c⟩ ⟨v,d⟩
  simp [pi, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite]

private lemma pi_mul (Y Z : Matrix b b ℂ) :
    pi (a := a) Y * pi Z = pi (a := a) (Y * Z) := by
  simp only [pi_eq_kronecker]
  simpa only [Matrix.one_mul, Matrix.kronecker] using
    (Matrix.mul_kronecker_mul Y Z (1 : Matrix (Env a b) (Env a b) ℂ) 1).symm

private lemma pi_star (Y : Matrix b b ℂ) :
    (pi (a := a) Y)ᴴ = pi Yᴴ := by
  ext ⟨u,c⟩ ⟨v,d⟩
  by_cases h : c = d
  · subst d
    simp [pi, Matrix.conjTranspose_apply]
  · have h' : d ≠ c := Ne.symm h
    simp [pi, Matrix.conjTranspose_apply, h, h']

lemma e_star (Φ : QuantumChannel a b) : (e Φ)ᴴ = e Φ := by
  simp [e]

lemma e_mul_self (Φ : QuantumChannel a b) : e Φ * e Φ = e Φ := by
  have hJ := J_isometry Φ
  let A := J Φ * (J Φ)ᴴ
  change (1 - A) * (1 - A) = 1 - A
  rw [sub_mul, mul_sub, Matrix.mul_one]
  have hAA : A * A = A := by
    dsimp [A]
    calc
      (J Φ * (J Φ)ᴴ) * (J Φ * (J Φ)ᴴ) =
          J Φ * ((J Φ)ᴴ * J Φ) * (J Φ)ᴴ := by simp [Matrix.mul_assoc]
      _ = J Φ * (1 : Matrix a a ℂ) * (J Φ)ᴴ := by rw [hJ]
      _ = J Φ * (J Φ)ᴴ := by simp
  rw [Matrix.mul_sub, Matrix.mul_one, hAA]
  simp [sub_self]

lemma Phi_factor (Φ : QuantumChannel a b) (Y : Matrix b b ℂ) :
    Phi Φ Y = (J Φ)ᴴ * pi (a := a) Y * J Φ := by
  exact (krausAdjoint_compression (K Φ) Y).symm

private lemma Phi_star (Φ : QuantumChannel a b) (Y : Matrix b b ℂ) :
    Phi Φ Yᴴ = (Phi Φ Y)ᴴ :=
  krausAdjoint_star (K Φ) Y

def defectR (Φ : QuantumChannel a b) {R : Type u}
    [Fintype R] [DecidableEq R] (Y : Matrix (R × b) (R × b) ℂ) :
    Matrix (R × a) (R × a) ℂ :=
  PhiR Φ (Y * Yᴴ) - PhiR Φ Y * (PhiR Φ Y)ᴴ

lemma PhiR_star (Φ : QuantumChannel a b)
    {R : Type u} [Fintype R] [DecidableEq R]
    (Y : Matrix (R × b) (R × b) ℂ) :
    PhiR Φ Yᴴ = (PhiR Φ Y)ᴴ := by
  ext ⟨r,x⟩ ⟨s,y⟩
  simp only [PhiR, Matrix.conjTranspose_apply]
  let Z : Matrix b b ℂ := fun u v => Y (s,u) (r,v)
  have hZ : Zᴴ = (fun u v => star (Y (s,v) (r,u))) := by
    ext u v
    rfl
  rw [← hZ, Phi_star]
  rfl

private lemma defectR_isHermitian (Φ : QuantumChannel a b)
    {R : Type u} [Fintype R] [DecidableEq R]
    (Y : Matrix (R × b) (R × b) ℂ) :
    (defectR Φ Y).IsHermitian := by
  rw [defectR]
  have hfirst : (PhiR Φ (Y * Yᴴ)).IsHermitian := by
    change (PhiR Φ (Y * Yᴴ))ᴴ = PhiR Φ (Y * Yᴴ)
    rw [← PhiR_star]
    simp [Matrix.conjTranspose_mul]
  have hsecond :
      (PhiR Φ Y * (PhiR Φ Y)ᴴ).IsHermitian :=
    Matrix.isHermitian_mul_conjTranspose_self _
  exact hfirst.sub hsecond

abbrev I (b : Type*) := b × b

def E (i : I b) : Matrix b b ℂ := Matrix.single i.1 i.2 1

private def packedY (i₀ : I b) : Matrix (I b × b) (I b × b) ℂ :=
  fun (i,x) (j,y) => if j = i₀ then E i x y else 0

def Cblock (Φ : QuantumChannel a b) (i : I b) :
    Matrix a (b × Env a b) ℂ :=
  (J Φ)ᴴ * pi (a := a) (E i) * e Φ

def C (Φ : QuantumChannel a b) :
    Matrix (I b × a) (b × Env a b) ℂ :=
  fun (i,x) p => Cblock Φ i x p

private lemma packed_product_block (i₀ i j : I b) :
    (fun u v => (packedY i₀ * (packedY i₀)ᴴ) (i,u) (j,v)) =
      E i * (E j)ᴴ := by
  classical
  ext u v
  simp only [packedY, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  simp [E, Matrix.conjTranspose_single, Finset.sum_ite_eq',
    Finset.mem_univ, mul_ite, ite_mul]

private lemma packed_C_gram_block (Φ : QuantumChannel a b) (i j : I b) (x y : a) :
    (C Φ * (C Φ)ᴴ) (i,x) (j,y) =
      (Cblock Φ i * (Cblock Φ j)ᴴ) x y := by
  simp only [C, Matrix.mul_apply, Matrix.conjTranspose_apply]

private lemma Cblock_gram (Φ : QuantumChannel a b) (i j : I b) :
    Cblock Φ i * (Cblock Φ j)ᴴ =
      Phi Φ (E i * (E j)ᴴ) - Phi Φ (E i) * (Phi Φ (E j))ᴴ := by
  simp only [Cblock, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    e_star]
  have hreg :
      ((J Φ)ᴴ * pi (a := a) (E i) * e Φ) *
          (e Φ * ((pi (a := a) (E j))ᴴ * J Φ)) =
        ((J Φ)ᴴ * pi (a := a) (E i)) * (e Φ * e Φ) *
          (pi (a := a) (E j))ᴴ * J Φ := by
    simp [Matrix.mul_assoc]
  rw [hreg, e_mul_self]
  simp only [Phi_factor, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, pi_star]
  rw [← pi_mul]
  simp [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc]

private lemma packed_Phi_block (Φ : QuantumChannel a b)
    (i₀ i j : I b) (x y : a) :
    PhiR Φ (packedY i₀) (i,x) (j,y) =
      if j = i₀ then Phi Φ (E i) x y else 0 := by
  classical
  by_cases h : j = i₀
  · simp [PhiR, Phi, packedY, E, h]
  · have hzero : krausAdjoint (K Φ) (fun _ _ : b => 0) = 0 := by
      change krausAdjoint (K Φ) (0 : Matrix b b ℂ) = 0
      simp [krausAdjoint]
    simp [PhiR, Phi, packedY, h, hzero]

private lemma packed_Phi_gram_block (Φ : QuantumChannel a b)
    (i₀ i j : I b) (x y : a) :
    (PhiR Φ (packedY i₀) * (PhiR Φ (packedY i₀))ᴴ) (i,x) (j,y) =
      (Phi Φ (E i) * (Phi Φ (E j))ᴴ) x y := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  simp [packed_Phi_block, mul_ite, ite_mul]

private lemma packed_defect_gram (Φ : QuantumChannel a b) (i₀ : I b) :
    defectR Φ (packedY i₀) = C Φ * (C Φ)ᴴ := by
  ext ⟨i,x⟩ ⟨j,y⟩
  rw [packed_C_gram_block, Cblock_gram]
  simp only [defectR, Matrix.sub_apply, PhiR]
  rw [packed_product_block]
  exact congrArg (fun M : Matrix a a ℂ => Phi Φ (E i * (E j)ᴴ) x y - M x y)
    (by ext u v; exact packed_Phi_gram_block Φ i₀ i j u v)

def D (Φ : QuantumChannel a b) (x : I b → ℂ) :
    Matrix (I b × a) a ℂ :=
  fun (i,u) v => (Phi Φ (E i) - x i • (1 : Matrix a a ℂ)) u v

private def residual (Φ : QuantumChannel a b) (i₀ : I b)
    (X : Matrix (I b) (I b) ℂ) : Matrix (I b × a) (I b × a) ℂ :=
  PhiR Φ (packedY i₀) - Matrix.kronecker X (1 : Matrix a a ℂ)

private def otherColumns (Φ : QuantumChannel a b) (i₀ : I b)
    (X : Matrix (I b) (I b) ℂ) : Matrix (I b × a) (I b × a) ℂ :=
  fun p (j,v) => if j = i₀ then 0 else residual Φ i₀ X p (j,v)

private lemma residual_selected (Φ : QuantumChannel a b) (i₀ : I b)
    (X : Matrix (I b) (I b) ℂ) (p : I b × a) (v : a) :
    residual Φ i₀ X p (i₀,v) = D Φ (fun i => X i i₀) p v := by
  rcases p with ⟨i,u⟩
  simp [residual, D, packed_Phi_block, Matrix.kronecker, Matrix.kroneckerMap_apply]

private lemma residual_gram_split (Φ : QuantumChannel a b) (i₀ : I b)
    (X : Matrix (I b) (I b) ℂ) :
    residual Φ i₀ X * (residual Φ i₀ X)ᴴ =
      D Φ (fun i => X i i₀) * (D Φ (fun i => X i i₀))ᴴ +
        otherColumns Φ i₀ X * (otherColumns Φ i₀ X)ᴴ := by
  classical
  ext p q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.add_apply]
  let f : I b → a → ℂ := fun j v =>
    residual Φ i₀ X p (j,v) * star (residual Φ i₀ X q (j,v))
  have hsplit : (∑ j, ∑ v, f j v) =
      (∑ v, f i₀ v) + ∑ j, ∑ v, if j = i₀ then 0 else f j v := by
    calc
      (∑ j, ∑ v, f j v) = ∑ j, ∑ v,
          ((if j = i₀ then f j v else 0) + (if j = i₀ then 0 else f j v)) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro v hv
        split_ifs <;> simp
      _ = _ := by simp [Finset.sum_add_distrib]
  have hother (j : I b) (v : a) :
      otherColumns Φ i₀ X p (j,v) * star (otherColumns Φ i₀ X q (j,v)) =
        if j = i₀ then 0 else f j v := by
    by_cases h : j = i₀ <;> simp [otherColumns, h, f]
  simpa only [Fintype.sum_prod_type, hother, f, residual_selected] using hsplit

/-- The original universal trace-inf premise, expressed on the actual
amplified trace adjoint. -/
def UniversalPositiveTraceTest (Φ : QuantumChannel a b) (k : ℝ) : Prop :=
  ∀ {R : Type u} [Fintype R] [DecidableEq R]
    (Y : Matrix (R × b) (R × b) ℂ)
    (Z : Matrix (R × a) (R × a) ℂ), Z.PosDef →
    sInf (Set.range (fun X : Matrix R R ℂ =>
      (Z * ((PhiR Φ Y - Matrix.kronecker X (1 : Matrix a a ℂ)) *
        Matrix.conjTranspose (PhiR Φ Y - Matrix.kronecker X (1 : Matrix a a ℂ)))).trace.re)) ≤
      (Z * ((k : ℂ) • defectR Φ Y)).trace.re

/-- The actual defect supplies the Hermitian target required by the
common-center theorem. -/
private lemma packed_common_center
    (Φ : QuantumChannel a b) (k : ℝ) (_hk : 0 ≤ k) (i₀ : I b)
    (hUniversal : UniversalPositiveTraceTest Φ k) :
    ∃ X : Matrix (I b) (I b) ℂ,
      (((k : ℂ) • defectR Φ (packedY i₀)) -
        (PhiR Φ (packedY i₀) - Matrix.kronecker X (1 : Matrix a a ℂ)) *
          Matrix.conjTranspose (PhiR Φ (packedY i₀) -
            Matrix.kronecker X (1 : Matrix a a ℂ))).PosSemidef := by
  let A := PhiR Φ (packedY i₀)
  let B := (k : ℂ) • defectR Φ (packedY i₀)
  have hB : B.IsHermitian := by
    change Bᴴ = B
    simp [B, Matrix.conjTranspose_smul, (defectR_isHermitian Φ (packedY i₀)).eq]
  obtain ⟨X, hX⟩ := exists_common_center_of_posDef_trace_inf_le A B hB (by
    intro Z hZ
    exact hUniversal (R := I b) (packedY i₀) Z hZ)
  exact ⟨X, hX⟩

/-- One actual scalar column controls the joint Gram of every basis
residual.  The discarded columns contribute a positive Gram remainder. -/
theorem selected_column_joint_gram
    (Φ : QuantumChannel a b) (k : ℝ) (hk : 0 ≤ k) (i₀ : I b)
    (hUniversal : UniversalPositiveTraceTest Φ k) :
    ∃ x : I b → ℂ,
      ((k : ℂ) • (C Φ * (C Φ)ᴴ) - D Φ x * (D Φ x)ᴴ).PosSemidef := by
  obtain ⟨X, hX⟩ := packed_common_center Φ k hk i₀ hUniversal
  refine ⟨fun i => X i i₀, ?_⟩
  change ((k : ℂ) • defectR Φ (packedY i₀) -
    residual Φ i₀ X * (residual Φ i₀ X)ᴴ).PosSemidef at hX
  rw [packed_defect_gram, residual_gram_split] at hX
  have hR := Matrix.posSemidef_self_mul_conjTranspose (otherColumns Φ i₀ X)
  convert hX.add hR using 1
  abel

/-! The remainder of this module is the actual common-state consumer.  The
following finite-dimensional transport keeps the heterogeneous Kraus columns
in their native rectangular matrix types while applying the repository's
Douglas and singular-polar suppliers. -/

private lemma e_norm_le (Φ : QuantumChannel a b)
    (z : EuclideanSpace ℂ (b × Env a b)) : ‖Matrix.toEuclideanLin (e Φ) z‖ ≤ ‖z‖ := by
  let P := Matrix.toEuclideanCLM (n := b × Env a b) (𝕜 := ℂ) (e Φ)
  have hp : IsStarProjection P := by
    have hp' : IsStarProjection (e Φ) := ⟨e_mul_self Φ, e_star Φ⟩
    exact hp'.map (Matrix.toEuclideanCLM (n := b × Env a b) (𝕜 := ℂ))
  have hpn := IsStarProjection.norm_le P hp
  exact (P.le_opNorm z).trans (by simpa using mul_le_mul_of_nonneg_right hpn (norm_nonneg z))

private lemma C_support (Φ : QuantumChannel a b) : C Φ * e Φ = C Φ := by
  ext ⟨i,x⟩ p
  change (Cblock Φ i * e Φ) x p = Cblock Φ i x p
  rw [Cblock, Matrix.mul_assoc, Matrix.mul_assoc, e_mul_self]
  simp [Matrix.mul_assoc]

private lemma supported_joint_factor (Φ : QuantumChannel a b) (k : ℝ) (hk : 0 ≤ k)
    (hUniversal : UniversalPositiveTraceTest Φ k) :
    ∃ (x : I b → ℂ) (T : Matrix (b × Env a b) a ℂ),
      C Φ * T = D Φ x ∧ e Φ * T = T ∧
      ((k : ℂ) • (1 : Matrix a a ℂ) - Tᴴ * T).PosSemidef := by
  obtain ⟨x, hx⟩ := selected_column_joint_gram Φ k hk (Classical.choice inferInstance) hUniversal
  obtain ⟨T₀, hT₀, hn⟩ := rectangular_douglas (C Φ) (D Φ x) k hk hx
  refine ⟨x, e Φ * T₀, ?_, ?_, norm_bound_gram _ k hk ?_⟩
  · rw [← Matrix.mul_assoc, C_support, hT₀]
  · rw [← Matrix.mul_assoc, e_mul_self]
  · intro z
    rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply]
    exact (e_norm_le Φ _).trans (hn z)

private lemma pi_one : pi (a := a) (1 : Matrix b b ℂ) = 1 := by
  ext ⟨u,c⟩ ⟨v,d⟩
  by_cases h : c = d <;> by_cases h' : u = v <;>
    simp [pi, Matrix.one_apply, Prod.mk.injEq, h, h']

private lemma pi_sum {ι : Type*} [Fintype ι] (Z : ι → Matrix b b ℂ) :
    pi (a := a) (∑ i, Z i) = ∑ i, pi (a := a) (Z i) := by
  ext ⟨u,c⟩ ⟨v,d⟩
  by_cases h : c = d <;> simp [pi, h, Matrix.sum_apply]

private lemma pi_smul (c : ℂ) (Z : Matrix b b ℂ) :
    pi (a := a) (c • Z) = c • pi (a := a) Z := by
  ext ⟨u,d⟩ ⟨v,f⟩
  by_cases h : d = f <;> simp [pi, h]

private lemma e_orthogonal (Φ : QuantumChannel a b) : (J Φ)ᴴ * e Φ = 0 := by
  simp [e, Matrix.mul_sub, ← Matrix.mul_assoc, J_isometry]

private def traceDensity (x : I b → ℂ) : Matrix b b ℂ := fun v u => x (u,v)

private lemma traceDensity_pairing (x : I b → ℂ) (Z : Matrix b b ℂ) :
    (traceDensity x * Z).trace = ∑ i : I b, Z i.1 i.2 * x i := by
  simp only [traceDensity, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  exact mul_comm _ _

private lemma linear_scalar_compression (Φ : QuantumChannel a b) (x : I b → ℂ)
    (T : Matrix (b × Env a b) a ℂ)
    (hCT : C Φ * T = D Φ x) (heT : e Φ * T = T) (Z : Matrix b b ℂ) :
    (J Φ)ᴴ * pi (a := a) Z * (J Φ - T) =
      (traceDensity x * Z).trace • (1 : Matrix a a ℂ) := by
  have hb (i : I b) : (J Φ)ᴴ * pi (a := a) (E i) * (J Φ - T) =
      x i • (1 : Matrix a a ℂ) := by
    have hi : Cblock Φ i * T = Phi Φ (E i) - x i • (1 : Matrix a a ℂ) := by
      ext u v
      exact congrArg (fun M => M (i,u) v) hCT
    have hT : (J Φ)ᴴ * pi (a := a) (E i) * T =
        Phi Φ (E i) - x i • (1 : Matrix a a ℂ) := by
      simpa only [Cblock, Matrix.mul_assoc, heT] using hi
    rw [Matrix.mul_sub, ← Phi_factor, hT]
    abel
  have hZ : Z = ∑ i : I b, Z i.1 i.2 • E i := by
    ext u v
    simp [E, Matrix.single, Matrix.sum_apply, Fintype.sum_prod_type,
      ite_and]
  rw [traceDensity_pairing]
  conv_lhs => rw [hZ, pi_sum]
  simp only [pi_smul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, hb, smul_smul, Finset.sum_smul]

private lemma supported_scalar_certificate (Φ : QuantumChannel a b) (k : ℝ) (hk : 0 ≤ k)
    (hUniversal : UniversalPositiveTraceTest Φ k) :
    ∃ (τ : Matrix b b ℂ) (T : Matrix (b × Env a b) a ℂ),
      τ.trace = 1 ∧ e Φ * T = T ∧ (J Φ)ᴴ * T = 0 ∧
      ((k : ℂ) • (1 : Matrix a a ℂ) - Tᴴ * T).PosSemidef ∧
      (J Φ - T)ᴴ * (J Φ - T) = 1 + Tᴴ * T ∧
      ∀ Z : Matrix b b ℂ, (J Φ)ᴴ * pi (a := a) Z * (J Φ - T) =
        (τ * Z).trace • (1 : Matrix a a ℂ) := by
  obtain ⟨x,T,hCT,heT,hbound⟩ := supported_joint_factor Φ k hk hUniversal
  have hJT : (J Φ)ᴴ * T = 0 := by
    rw [← heT, ← Matrix.mul_assoc, e_orthogonal, Matrix.zero_mul]
  have hTJ : Tᴴ * J Φ = 0 := by
    simpa using congrArg Matrix.conjTranspose hJT
  have hscalar := linear_scalar_compression Φ x T hCT heT
  have hone := hscalar (1 : Matrix b b ℂ)
  rw [pi_one, Matrix.mul_one, Matrix.mul_sub, J_isometry, hJT, sub_zero,
    Matrix.mul_one] at hone
  have htrace : (traceDensity x).trace = 1 := by
    let u : a := Classical.choice inferInstance
    have hdiag := congrArg (fun M : Matrix a a ℂ => M u u) hone
    simpa using hdiag.symm
  refine ⟨traceDensity x,T,htrace,heT,hJT,hbound,?_,hscalar⟩
  simp [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub,
    J_isometry, hJT, hTJ]

section SquareEuclidean
open scoped Matrix.Norms.L2Operator

private abbrev matrixOfCLM {n : Type*} [Fintype n] [DecidableEq n]
    (A : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) : Matrix n n ℂ :=
  (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm A

private lemma matrixOfCLM_pos {n : Type*} [Fintype n] [DecidableEq n]
    (A : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hA : 0 ≤ A) : (matrixOfCLM A).PosSemidef := by
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    show (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) (matrixOfCLM A) = A from
      (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).apply_symm_apply A]
  exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hA).toLinearMap

private lemma matrixCLM_trace {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ n) (matrixCLM M).toLinearMap = M.trace := by
  change LinearMap.trace ℂ _ (Matrix.toEuclideanLin M) = _
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]

private lemma finite_trace_norm (A : EuclideanSpace ℂ b →L[ℂ] EuclideanSpace ℂ b) :
    ‖(matrixOfCLM A).trace‖ ≤ (matrixOfCLM (CFC.abs A)).trace.re := by
  let h := isTraceClass_of_finiteDimensional A
  let B := h.choose_spec.choose
  letI : Finite h.choose := B.orthonormal.linearIndependent.finite
  letI : Fintype h.choose := Fintype.ofFinite h.choose
  have ht : trace A h = (matrixOfCLM A).trace := by
    rw [_root_.trace, ← trace_eq_sum_inner_hilbertBasis_of_finiteDimensional A B]
    have hA : matrixCLM (matrixOfCLM A) = A :=
      (Matrix.toEuclideanCLM (n := b) (𝕜 := ℂ)).apply_symm_apply A
    simpa only [hA] using matrixCLM_trace (matrixOfCLM A)
  have hn : traceNorm A h = (matrixOfCLM (CFC.abs A)).trace.re := by
    have hs := congrArg Complex.re
      (trace_eq_sum_inner_hilbertBasis_of_finiteDimensional (CFC.abs A) B)
    rw [tsum_fintype] at hs
    have hm := matrixCLM_trace (matrixOfCLM (CFC.abs A))
    have hA : matrixCLM (matrixOfCLM (CFC.abs A)) = CFC.abs A :=
      (Matrix.toEuclideanCLM (n := b) (𝕜 := ℂ)).apply_symm_apply (CFC.abs A)
    rw [hA] at hm
    rw [traceNorm, tsum_fintype]
    simpa [hm] using hs.symm
  simpa [ht, hn] using TraceClass.norm_trace_le h

private lemma polar_matrix_certificate (τ : Matrix b b ℂ) (hτ : τ.trace = 1) :
    ∃ (S U : Matrix b b ℂ), S.PosSemidef ∧ Uᴴ * τ = S ∧
      (1 - U * Uᴴ).PosSemidef ∧ 1 ≤ S.trace.re ∧
      S.trace = (S.trace.re : ℂ) := by
  let F := Matrix.toEuclideanCLM (n := b) (𝕜 := ℂ)
  let A := F τ
  let V := Polar.polarFactor A
  let S := matrixOfCLM (Polar.absOperator A)
  let U := matrixOfCLM V
  have hS : S.PosSemidef := matrixOfCLM_pos _ (CFC.abs_nonneg A)
  have hUS : Uᴴ * τ = S := by
    have h := congrArg matrixOfCLM (Polar.star_polarFactor_mul_self A)
    simpa only [U, S, V, A, F, matrixOfCLM, map_mul, map_star,
      StarAlgEquiv.symm_apply_apply, Matrix.star_eq_conjTranspose] using h
  have hUnorm : ∀ z : EuclideanSpace ℂ b, ‖Matrix.toEuclideanLin Uᴴ z‖ ≤ ‖z‖ := by
    intro z
    change ‖F Uᴴ z‖ ≤ ‖z‖
    rw [← Matrix.star_eq_conjTranspose, map_star]
    have hU : F U = V := F.apply_symm_apply V
    rw [hU, ContinuousLinearMap.star_eq_adjoint]
    have hn : ‖V.adjoint‖ ≤ 1 := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact Polar.polarFactor_opNorm_le A
    exact (V.adjoint.le_opNorm z).trans (by
      simpa only [one_mul] using (mul_le_mul_of_nonneg_right hn (norm_nonneg z)))
  have hUU : (1 - U * Uᴴ).PosSemidef := by
    simpa using norm_bound_gram Uᴴ 1 (by norm_num) (by simpa using hUnorm)
  refine ⟨S,U,hS,hUS,hUU,?_,?_⟩
  · have h := finite_trace_norm A
    simpa [A, F, S, matrixOfCLM, Polar.absOperator, hτ] using h
  · exact Complex.ext rfl (by
      simpa using (Complex.nonneg_iff.mp hS.trace_nonneg).2.symm)

end SquareEuclidean

private lemma polar_trace_cyclic (τ S U Z : Matrix b b ℂ)
    (hUS : Uᴴ * τ = S) :
    (τ * (Z * Uᴴ)).trace = (S * Z).trace := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  rw [hUS]

private lemma positive_state_from_certificate (τ : Matrix b b ℂ) (hτ : τ.trace = 1) :
    ∃ (σ : DensityState b) (U S : Matrix b b ℂ) (t : ℝ),
      S.PosSemidef ∧ Uᴴ * τ = S ∧ 1 ≤ t ∧ S.trace = (t : ℂ) ∧
      (1 - U * Uᴴ).PosSemidef ∧
      CStarMatrix.ofMatrix.symm σ.1 = (t⁻¹ : ℂ) • S := by
  obtain ⟨S,U,hS,hUS,hUU,ht,htr⟩ := polar_matrix_certificate τ hτ
  have htpos : 0 < S.trace.re := lt_of_lt_of_le (by norm_num) ht
  let t : ℝ := S.trace.re
  have htr' : S.trace = (t : ℂ) := by simpa [t] using htr
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt htpos)
  have hσ : ((t⁻¹ : ℂ) • S).PosSemidef :=
    hS.smul (inv_nonneg.mpr (by exact_mod_cast htpos.le))
  let σ : DensityState b := by
    refine ⟨CStarMatrix.ofMatrix ((t⁻¹ : ℂ) • S), ?_, ?_⟩
    · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      exact Matrix.PosSemidef.nonneg hσ
    · change Matrix.trace ((t⁻¹ : ℂ) • S) = 1
      rw [Matrix.trace_smul, htr']
      change (t : ℂ)⁻¹ * (t : ℂ) = 1
      exact inv_mul_cancel₀ ht0
  refine ⟨σ,U,S,t,hS,hUS,ht,htr',hUU,?_⟩
  rfl

private lemma pi_sub (Y Z : Matrix b b ℂ) :
    pi (a := a) (Y - Z) = pi (a := a) Y - pi (a := a) Z := by
  ext ⟨u,c⟩ ⟨v,d⟩
  by_cases h : c = d <;> simp [pi, h]

private lemma pi_pos {Z : Matrix b b ℂ} (hZ : Z.PosSemidef) :
    (pi (a := a) Z).PosSemidef := by
  rw [pi_eq_kronecker]
  exact hZ.kronecker Matrix.PosSemidef.one

private lemma supported_gram_flip (Φ : QuantumChannel a b)
    (T : Matrix (b × Env a b) a ℂ) (k : ℝ) (hk : 0 ≤ k)
    (heT : e Φ * T = T)
    (hT : ((k : ℂ) • (1 : Matrix a a ℂ) - Tᴴ * T).PosSemidef) :
    ((k : ℂ) • e Φ - T * Tᴴ).PosSemidef := by
  have hn : ∀ z : EuclideanSpace ℂ a, ‖matrixCLM T z‖ ≤ Real.sqrt k * ‖z‖ := by
    have h := gram_majorization (1 : Matrix a a ℂ) Tᴴ k hk (by simpa using hT)
    simpa [matrixCLM, Matrix.toEuclideanLin] using h
  have hop : ‖matrixCLM T‖ ≤ Real.sqrt k :=
    ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg k) hn
  have hop' : ‖matrixCLM Tᴴ‖ ≤ Real.sqrt k := by
    rw [← matrixCLM_adjoint, ContinuousLinearMap.adjoint.norm_map]
    exact hop
  have hflip : ((k : ℂ) • (1 : Matrix (b × Env a b) (b × Env a b) ℂ) -
      T * Tᴴ).PosSemidef := by
    simpa using norm_bound_gram Tᴴ k hk (fun z =>
      ((matrixCLM Tᴴ).le_opNorm z).trans (mul_le_mul_of_nonneg_right hop' (norm_nonneg z)))
  have hc := hflip.mul_mul_conjTranspose_same (e Φ)
  have hTe : Tᴴ * e Φ = Tᴴ := by
    simpa [e_star] using congrArg Matrix.conjTranspose heT
  have hceq : e Φ * (((k : ℂ) • (1 : Matrix (b × Env a b) (b × Env a b) ℂ)) -
      T * Tᴴ) * e Φ = (k : ℂ) • e Φ - T * Tᴴ := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one]
    rw [e_mul_self, ← Matrix.mul_assoc (e Φ) T Tᴴ, heT,
      Matrix.mul_assoc T Tᴴ (e Φ), hTe]
  rw [e_star, hceq] at hc
  exact hc

theorem common_positive_state_compression
    (Φ : QuantumChannel a b) (k : ℝ) (hk : 0 ≤ k)
    (hUniversal : UniversalPositiveTraceTest Φ k) :
    ∃ (σ : DensityState b) (W K : Matrix (b × Env a b) a ℂ),
      (J Φ)ᴴ * W = 1 ∧ e Φ * W = W - J Φ ∧ K = J Φ - W ∧
      (J Φ)ᴴ * K = 0 ∧ e Φ * K = K ∧
      ((k : ℂ) • e Φ - K * Kᴴ).PosSemidef ∧
      ∀ Z : Matrix b b ℂ,
        (J Φ)ᴴ * pi (a := a) Z * W =
          (((CStarMatrix.ofMatrix.symm σ.1 : Matrix b b ℂ) * Z).trace) •
            (1 : Matrix a a ℂ) := by
  obtain ⟨τ,T,hτ,heT,hJT,hbound,hWnorm,hscalar⟩ :=
    supported_scalar_certificate Φ k hk hUniversal
  obtain ⟨σ,U,S,t,hS,hUS,ht,htr,hUU,hσ⟩ := positive_state_from_certificate τ hτ
  let W := (t⁻¹ : ℂ) • (pi (a := a) Uᴴ * (J Φ - T))
  have ht0 : (t : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le (by norm_num) ht))
  have hcomp : ∀ Z : Matrix b b ℂ,
      (J Φ)ᴴ * pi (a := a) Z * W =
        (((CStarMatrix.ofMatrix.symm σ.1 : Matrix b b ℂ) * Z).trace) •
          (1 : Matrix a a ℂ) := by
    intro Z
    dsimp [W]
    rw [Matrix.mul_smul]
    have hm : (J Φ)ᴴ * pi (a := a) Z *
          (pi (a := a) Uᴴ * (J Φ - T)) =
        (J Φ)ᴴ * pi (a := a) (Z * Uᴴ) * (J Φ - T) := by
      calc
        (J Φ)ᴴ * pi (a := a) Z * (pi (a := a) Uᴴ * (J Φ - T)) =
            (J Φ)ᴴ * (pi (a := a) Z * pi (a := a) Uᴴ) * (J Φ - T) := by
              simp only [Matrix.mul_assoc]
        _ = (J Φ)ᴴ * pi (a := a) (Z * Uᴴ) * (J Φ - T) := by
              rw [pi_mul]
    rw [hm]
    rw [hscalar]
    have hcyc := polar_trace_cyclic τ S U Z hUS
    rw [hcyc, hσ, Matrix.smul_mul, Matrix.trace_smul]
    simp only [smul_smul, smul_eq_mul]
  let K : Matrix (b × Env a b) a ℂ := J Φ - W
  have hW : (J Φ)ᴴ * W = 1 := by
    have h := hcomp (1 : Matrix b b ℂ)
    rw [pi_one, Matrix.mul_one, Matrix.mul_one] at h
    have htrσ : Matrix.trace (CStarMatrix.ofMatrix.symm σ.1) = 1 := σ.trace_eq_one
    simpa [htrσ] using h
  have heW : e Φ * W = W - J Φ := by
    rw [e, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hW, Matrix.mul_one]
  have hKorth : (J Φ)ᴴ * K = 0 := by
    dsimp [K]
    rw [Matrix.mul_sub, J_isometry, hW]
    simp
  have heJ : e Φ * J Φ = 0 := by
    rw [e, Matrix.sub_mul, Matrix.mul_assoc, J_isometry]
    simp
  have heK : e Φ * K = K := by
    dsimp [K]
    rw [Matrix.mul_sub, heJ, heW]
    abel
  let q : ℝ := t⁻¹ * t⁻¹
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hq0 : 0 ≤ q := mul_nonneg (inv_nonneg.mpr htpos.le) (inv_nonneg.mpr htpos.le)
  have hq1 : q ≤ 1 := by
    have hi : t⁻¹ ≤ 1 := (inv_le_one₀ htpos).mpr ht
    exact (mul_le_mul hi hi (inv_nonneg.mpr htpos.le) (by norm_num)).trans (by norm_num)
  have hQ : (1 - (q : ℂ) • pi (a := a) (U * Uᴴ)).PosSemidef := by
    have h1 := (Matrix.PosSemidef.one (n := b × Env a b) (R := ℂ)).smul
      (show (0 : ℂ) ≤ ((1-q : ℝ) : ℂ) by exact_mod_cast sub_nonneg.mpr hq1)
    have h2 := (pi_pos (a := a) hUU).smul
      (show (0 : ℂ) ≤ (q : ℂ) by exact_mod_cast hq0)
    rw [pi_sub, pi_one] at h2
    convert h1.add h2 using 1
    simp only [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul,
      smul_sub]
    abel
  have hWW : Wᴴ * W = (q : ℂ) •
      ((J Φ - T)ᴴ * pi (a := a) (U * Uᴴ) * (J Φ - T)) := by
    simp [W, q, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, pi_star,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← pi_mul, Matrix.mul_assoc,
      Complex.ofReal_mul, Complex.ofReal_inv]
  have hKJ : Kᴴ * J Φ = 0 := by
    simpa using congrArg Matrix.conjTranspose hKorth
  have hKK : Kᴴ * K = Wᴴ * W - 1 := by
    have hKW : W = J Φ - K := by dsimp [K]; abel
    rw [hKW]
    simp [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, J_isometry,
      hKorth, hKJ]
  have hdiff : (Tᴴ * T - Kᴴ * K).PosSemidef := by
    have hc := hQ.conjTranspose_mul_mul_same (J Φ - T)
    have heq : (J Φ - T)ᴴ *
          (1 - (q : ℂ) • pi (a := a) (U * Uᴴ)) * (J Φ - T) =
        (Tᴴ * T - Kᴴ * K) := by
      calc
        (J Φ - T)ᴴ * (1 - (q : ℂ) • pi (a := a) (U * Uᴴ)) * (J Φ - T) =
            (J Φ - T)ᴴ * (J Φ - T) -
              (q : ℂ) • ((J Φ - T)ᴴ * pi (a := a) (U * Uᴴ) * (J Φ - T)) := by
                have halg (V : Matrix (b × Env a b) a ℂ) :
                    Vᴴ * (1 - (q : ℂ) • pi (a := a) (U * Uᴴ)) * V =
                    Vᴴ * V - (q : ℂ) • (Vᴴ * pi (a := a) (U * Uᴴ) * V) := by
                  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
                    Matrix.mul_smul, Matrix.smul_mul]
                exact halg _
        _ = (1 + Tᴴ * T) - Wᴴ * W := by rw [hWnorm, hWW]
        _ = Tᴴ * T - Kᴴ * K := by rw [hKK]; abel
    rw [heq] at hc
    exact hc
  have hKbound : ((k : ℂ) • (1 : Matrix a a ℂ) - Kᴴ * K).PosSemidef := by
    convert hbound.add hdiff using 1
    abel
  exact ⟨σ,W,K,hW,heW,rfl,hKorth,heK,
    supported_gram_flip Φ K k hk heK hKbound,hcomp⟩

#print axioms selected_column_joint_gram
#print axioms common_positive_state_compression

end D5.S3.Quantum.Divergence.UniversalPositiveScalarizer
