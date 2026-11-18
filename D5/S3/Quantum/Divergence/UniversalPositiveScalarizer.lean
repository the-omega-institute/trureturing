/- GID: D5/S3/Quantum/Divergence/UniversalPositiveScalarizer
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/UniversalPositiveScalarizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One positive state controls both completely amplified channel residual Grams. -/

import D5.S3.Quantum.Divergence.CanonicalRelativeModularModel
import D5.S3.Quantum.Divergence.UniversalCommonCenter
import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Quantum.Divergence.ScalarizerMatrixTransport
import D5.S3.Quantum.Analysis.TraceClass.Polar
import D5.S3.Quantum.Analysis.TraceClass.Basic
import D5.S3.Quantum.Analysis.TraceClass.Pairing
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

/-! A common positive state from universal positive trace tests.

The canonical Kraus column supplies the actual adjoint and defect Gram.
A common matrix center has one selected column; all its other columns remain
as a positive Gram remainder. The consumer below turns this selected joint
Gram into one singular-polar positive trace-one output state and proves its
compression identity through every finite reference amplification.

-/

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
open D5.S3.Quantum.Divergence.ScalarizerMatrixTransport

universe u

variable {a b : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]

abbrev Env (a b : Type*) [Fintype a] [Fintype b] :=
  Fin (Fintype.card b) × Fin (Fintype.card a)

abbrev K (Φ : QuantumChannel a b) : Env a b → Matrix b a ℂ :=
  (actual_kraus_representation Φ).kraus

/-- The actual Stinespring column, with output index first as required by the
canonical Kraus convention. -/
def J (Φ : QuantumChannel a b) : Matrix (b × Env a b) a ℂ :=
  fun p x => K Φ p.2 p.1 x

private lemma J_isometry (Φ : QuantumChannel a b) :
    Matrix.conjTranspose (J Φ) * J Φ = 1 := by
  classical
  ext x y
  simp only [J, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  have h0 : (∑ c : Env a b, ∑ u : b,
      star (K Φ c u x) * K Φ c u y) = if x = y then 1 else 0 := by
    simpa [K, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply] using
      congrArg (fun M => M x y) (actual_kraus_representation Φ).hkraus
  rw [Finset.sum_comm]
  exact h0

/-- The actual output-to-input trace adjoint, written directly from the
canonical normalized Kraus family. -/
def Phi (Φ : QuantumChannel a b) (Y : Matrix b b ℂ) : Matrix a a ℂ :=
  fun x y => ∑ c : Env a b, ∑ u : b, ∑ v : b,
    star (K Φ c u x) * Y u v * K Φ c v y

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

private lemma e_star (Φ : QuantumChannel a b) : (e Φ)ᴴ = e Φ := by
  simp [e]

private lemma e_mul_self (Φ : QuantumChannel a b) : e Φ * e Φ = e Φ := by
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

private lemma Phi_factor (Φ : QuantumChannel a b) (Y : Matrix b b ℂ) :
    Phi Φ Y = (J Φ)ᴴ * pi (a := a) Y * J Φ := by
  ext x y
  let f : (Fin (Fintype.card b)) → (Fin (Fintype.card a)) → b → b → ℂ :=
    fun c d u v => star (K Φ (c,d) u x) * (Y u v * K Φ (c,d) v y)
  have hswap : (∑ c, ∑ d, ∑ u, ∑ v, f c d u v) =
      ∑ v, ∑ c, ∑ d, ∑ u, f c d u v := by
    calc
      (∑ c, ∑ d, ∑ u, ∑ v, f c d u v) =
          ∑ c, ∑ d, ∑ v, ∑ u, f c d u v := by
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.sum_comm]
      _ = ∑ v, ∑ c, ∑ d, ∑ u, f c d u v := by
        calc
          (∑ c, ∑ d, ∑ v, ∑ u, f c d u v) =
              ∑ c, ∑ v, ∑ d, ∑ u, f c d u v := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [Finset.sum_comm]
          _ = ∑ v, ∑ c, ∑ d, ∑ u, f c d u v := by
            rw [Finset.sum_comm]
  simpa [Phi, J, pi, Matrix.mul_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum, mul_assoc, f] using hswap

private lemma Phi_star (Φ : QuantumChannel a b) (Y : Matrix b b ℂ) :
    Phi Φ Yᴴ = (Phi Φ Y)ᴴ := by
  rw [Phi_factor, Phi_factor]
  simp [Matrix.conjTranspose_mul, pi_star, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

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
  · simp [PhiR, Phi, packedY, h]

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
    (z : EuclideanSpace ℂ (b × Env a b)) : ‖matrixCLM (e Φ) z‖ ≤ ‖z‖ := by
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
    rw [matrixCLM_mul, ContinuousLinearMap.comp_apply]
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

/-! The next transport is deliberately kept local to this consumer.  It turns
the native Euclidean continuous maps supplied by the polar library back into
the matrix representation already used by `J`, `pi`, and `e`. -/

private def matrixOfCLM {n : Type*} [Fintype n] [DecidableEq n]
    (A : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) : Matrix n n ℂ :=
  Matrix.toEuclideanLin.symm A.toLinearMap

private lemma matrixCLM_matrixOfCLM {n : Type*} [Fintype n] [DecidableEq n]
    (A : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    matrixCLM (matrixOfCLM A) = A := by
  apply ContinuousLinearMap.ext
  intro z
  change Matrix.toEuclideanLin (matrixOfCLM A) z = A z
  unfold matrixOfCLM
  rw [Matrix.toEuclideanLin.apply_symm_apply]
  rfl

private lemma matrixOfCLM_matrixCLM {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) : matrixOfCLM (matrixCLM M) = M := by
  unfold matrixOfCLM matrixCLM
  simp

private lemma matrixOfCLM_mul {n : Type*} [Fintype n] [DecidableEq n]
    (A B : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    matrixOfCLM (A * B) = matrixOfCLM A * matrixOfCLM B := by
  apply Matrix.toEuclideanLin.injective
  unfold matrixOfCLM
  rw [Matrix.toEuclideanLin.apply_symm_apply]
  change (A * B).toLinearMap = _
  rw [Matrix.toLpLin_mul_same]
  simp only [LinearEquiv.apply_symm_apply]
  rfl

private lemma matrixOfCLM_star {n : Type*} [Fintype n] [DecidableEq n]
    (A : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    matrixOfCLM (star A) = (matrixOfCLM A)ᴴ := by
  apply Matrix.toEuclideanLin.injective
  unfold matrixOfCLM
  rw [Matrix.toEuclideanLin.apply_symm_apply]
  change (star A).toLinearMap = _
  simp only [ContinuousLinearMap.star_eq_adjoint,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  simp only [LinearEquiv.apply_symm_apply]
  exact (congrArg ContinuousLinearMap.toLinearMap
    (LinearMap.adjoint_toContinuousLinearMap A.toLinearMap)).symm

private lemma matrixOfCLM_pos {n : Type*} [Fintype n] [DecidableEq n]
    (A : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hA : 0 ≤ A) : (matrixOfCLM A).PosSemidef := by
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  simpa [matrixOfCLM] using
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hA).toLinearMap

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
    simpa [matrixCLM_matrixOfCLM] using matrixCLM_trace (matrixOfCLM A)
  have hn : traceNorm A h = (matrixOfCLM (CFC.abs A)).trace.re := by
    have hs := congrArg Complex.re
      (trace_eq_sum_inner_hilbertBasis_of_finiteDimensional (CFC.abs A) B)
    rw [tsum_fintype] at hs
    have hm := matrixCLM_trace (matrixOfCLM (CFC.abs A))
    rw [matrixCLM_matrixOfCLM] at hm
    rw [traceNorm, tsum_fintype]
    simpa [hm] using hs.symm
  simpa [ht, hn] using TraceClass.norm_trace_le h

private lemma polar_matrix_certificate (τ : Matrix b b ℂ) (hτ : τ.trace = 1) :
    ∃ (S U : Matrix b b ℂ), S.PosSemidef ∧ Uᴴ * τ = S ∧
      (1 - U * Uᴴ).PosSemidef ∧ 1 ≤ S.trace.re ∧
      S.trace = (S.trace.re : ℂ) := by
  let A := matrixCLM τ
  let V := Polar.polarFactor A
  let S := matrixOfCLM (Polar.absOperator A)
  let U := matrixOfCLM V
  have hS : S.PosSemidef := matrixOfCLM_pos _ (CFC.abs_nonneg A)
  have hUS : Uᴴ * τ = S := by
    have h := congrArg matrixOfCLM (Polar.star_polarFactor_mul_self A)
    simpa [U, S, V, A, matrixOfCLM_mul, matrixOfCLM_star,
      matrixOfCLM_matrixCLM] using h
  have hUnorm : ∀ z : EuclideanSpace ℂ b, ‖matrixCLM Uᴴ z‖ ≤ ‖z‖ := by
    intro z
    have hU : matrixCLM U = V := matrixCLM_matrixOfCLM V
    rw [← matrixCLM_adjoint, hU]
    have hn : ‖V.adjoint‖ ≤ 1 := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact Polar.polarFactor_opNorm_le A
    exact (V.adjoint.le_opNorm z).trans (by
      simpa only [one_mul] using (mul_le_mul_of_nonneg_right hn (norm_nonneg z)))
  have hUU : (1 - U * Uᴴ).PosSemidef := by
    simpa using norm_bound_gram Uᴴ 1 (by norm_num) (by simpa using hUnorm)
  refine ⟨S,U,hS,hUS,hUU,?_,?_⟩
  · have h := finite_trace_norm A
    simpa [A, S, Polar.absOperator, matrixOfCLM_matrixCLM, hτ] using h
  · exact Complex.ext rfl (by
      simpa using (Complex.nonneg_iff.mp hS.trace_nonneg).2.symm)

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

private lemma common_positive_state_compression
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

private def amp {R m n : Type*} [DecidableEq R]
    (M : Matrix m n ℂ) : Matrix (R × m) (R × n) ℂ :=
  (1 : Matrix R R ℂ) ⊗ₖ M

private def piAmp {R : Type u} [Fintype R] [DecidableEq R]
    (Y : Matrix (R × b) (R × b) ℂ) :
    Matrix (R × (b × Env a b)) (R × (b × Env a b)) ℂ :=
  (Y ⊗ₖ (1 : Matrix (Env a b) (Env a b) ℂ)).submatrix
    (Equiv.prodAssoc R b (Env a b)).symm (Equiv.prodAssoc R b (Env a b)).symm

private lemma amp_mul {R m n p : Type*} [Fintype R] [DecidableEq R]
    [Fintype n] (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    amp (R := R) A * amp (R := R) B = amp (R := R) (A * B) := by
  simp only [amp]
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

private lemma amp_star {R m n : Type*} [DecidableEq R]
    (A : Matrix m n ℂ) : (amp (R := R) A)ᴴ = amp (R := R) Aᴴ := by
  simp [amp, Matrix.conjTranspose_kronecker]

private lemma piAmp_mul {R : Type u} [Fintype R] [DecidableEq R]
    (Y Z : Matrix (R × b) (R × b) ℂ) :
    piAmp (a := a) Y * piAmp (a := a) Z = piAmp (a := a) (Y * Z) := by
  unfold piAmp
  rw [Matrix.submatrix_mul_equiv _ _ _ (Equiv.prodAssoc R b (Env a b)).symm,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]

private lemma piAmp_star {R : Type u} [Fintype R] [DecidableEq R]
    (Y : Matrix (R × b) (R × b) ℂ) :
    (piAmp (a := a) Y)ᴴ = piAmp (a := a) Yᴴ := by
  simp [piAmp, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker]

private lemma piAmp_mul_amp {R : Type u} [Fintype R] [DecidableEq R]
    (B : Matrix (b × Env a b) a ℂ) (Y : Matrix (R × b) (R × b) ℂ)
    (r s : R) (p : b × Env a b) (y : a) :
    (piAmp (a := a) Y * amp (R := R) B) (r,p) (s,y) =
      (pi (a := a) (Y.submatrix (fun u => (r,u)) (fun v => (s,v))) * B) p y := by
  rcases p with ⟨u,c⟩
  simp only [Matrix.mul_apply, piAmp, amp, Matrix.kronecker_apply,
    Matrix.submatrix_apply, Equiv.prodAssoc_symm_apply, Fintype.sum_prod_type]
  simp [pi, Matrix.one_apply, mul_ite, ite_mul, Finset.sum_mul, Finset.mul_sum]

private lemma amp_compression {R : Type u} [Fintype R] [DecidableEq R]
    (A B : Matrix (b × Env a b) a ℂ)
    (Y : Matrix (R × b) (R × b) ℂ) (r s : R) (x y : a) :
    ((amp (R := R) A)ᴴ * piAmp (a := a) Y * amp (R := R) B) (r,x) (s,y) =
      (Aᴴ * pi (a := a) (Y.submatrix (fun u => (r,u)) (fun v => (s,v))) * B) x y := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Fintype.sum_prod_type]
  simp_rw [piAmp_mul_amp]
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp [amp, Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.kronecker_apply,
    apply_ite, ite_mul, Matrix.mul_apply, Fintype.sum_prod_type]

private lemma PhiR_factor {R : Type u} [Fintype R] [DecidableEq R]
    (Φ : QuantumChannel a b) (Y : Matrix (R × b) (R × b) ℂ) :
    PhiR Φ Y = (amp (R := R) (J Φ))ᴴ * piAmp (a := a) Y * amp (R := R) (J Φ) := by
  ext ⟨r,x⟩ ⟨s,y⟩
  rw [amp_compression]
  exact congrArg (fun M : Matrix a a ℂ => M x y)
    (Phi_factor Φ (Y.submatrix (fun u => (r,u)) (fun v => (s,v))))

/-- The weighted ordinary partial-trace center. -/
def stateCenter {R : Type u} [Fintype R] [DecidableEq R]
    (σ : DensityState b) (Y : Matrix (R × b) (R × b) ℂ) : Matrix R R ℂ :=
  fun r s => ((CStarMatrix.ofMatrix.symm σ.1 : Matrix b b ℂ) *
    Y.submatrix (fun u => (r,u)) (fun v => (s,v))).trace

private lemma stateCenter_partialTrace {R : Type u} [Fintype R] [DecidableEq R]
    (σ : DensityState b) (Y : Matrix (R × b) (R × b) ℂ) :
    stateCenter σ Y =
      D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight
        (((1 : Matrix R R ℂ) ⊗ₖ (CStarMatrix.ofMatrix.symm σ.1 : Matrix b b ℂ)) * Y) := by
  ext r s
  simp [stateCenter, Matrix.trace, Matrix.mul_apply, Matrix.kronecker_apply,
    D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
    Fintype.sum_prod_type, Matrix.one_apply, ite_mul]

private lemma amp_state_compression {R : Type u} [Fintype R] [DecidableEq R]
    (Φ : QuantumChannel a b) (σ : DensityState b)
    (W : Matrix (b × Env a b) a ℂ)
    (hW : ∀ Z : Matrix b b ℂ, (J Φ)ᴴ * pi (a := a) Z * W =
      ((CStarMatrix.ofMatrix.symm σ.1 : Matrix b b ℂ) * Z).trace • (1 : Matrix a a ℂ))
    (Y : Matrix (R × b) (R × b) ℂ) :
    (amp (R := R) (J Φ))ᴴ * piAmp (a := a) Y * amp (R := R) W =
      stateCenter σ Y ⊗ₖ (1 : Matrix a a ℂ) := by
  ext ⟨r,x⟩ ⟨s,y⟩
  rw [amp_compression, hW]
  rfl

private lemma amp_sub {R m n : Type*} [DecidableEq R]
    (A B : Matrix m n ℂ) : amp (R := R) (A - B) =
      amp (R := R) A - amp (R := R) B := by
  ext ⟨r,i⟩ ⟨s,j⟩
  simp [amp, mul_sub]

private lemma amp_smul {R m n : Type*} [DecidableEq R]
    (c : ℂ) (A : Matrix m n ℂ) : amp (R := R) (c • A) =
      c • amp (R := R) A := by
  simp [amp, Matrix.kronecker_smul]

private lemma amp_one {R m : Type*} [DecidableEq R] [DecidableEq m] :
    amp (R := R) (1 : Matrix m m ℂ) = 1 := Matrix.one_kronecker_one

private lemma amp_pos {R m : Type*} [Fintype R] [DecidableEq R]
    [Fintype m] [DecidableEq m] {A : Matrix m m ℂ} (hA : A.PosSemidef) :
    (amp (R := R) A).PosSemidef := by
  exact Matrix.PosSemidef.one.kronecker hA

private lemma amp_supported_flip {R : Type u} [Fintype R] [DecidableEq R]
    (Φ : QuantumChannel a b) (K : Matrix (b × Env a b) a ℂ) (k : ℝ)
    (hK : ((k : ℂ) • e Φ - K * Kᴴ).PosSemidef) :
    ((k : ℂ) • amp (R := R) (e Φ) -
      amp (R := R) K * (amp (R := R) K)ᴴ).PosSemidef := by
  have h := amp_pos (R := R) hK
  rw [amp_sub, amp_smul, ← amp_mul, ← amp_star] at h
  exact h

private lemma amplified_defect {R : Type u} [Fintype R] [DecidableEq R]
    (Φ : QuantumChannel a b) (Y : Matrix (R × b) (R × b) ℂ) :
    defectR Φ Y =
      (amp (R := R) (J Φ))ᴴ * piAmp (a := a) Y *
        amp (R := R) (e Φ) * (piAmp (a := a) Y)ᴴ * amp (R := R) (J Φ) := by
  rw [defectR, PhiR_factor, PhiR_factor]
  rw [← piAmp_mul, ← piAmp_star]
  simp [e, amp_sub, amp_one, ← amp_mul, ← amp_star, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    Matrix.mul_sub, Matrix.sub_mul]

set_option maxHeartbeats 800000 in
lemma defectR_posSemidef {R : Type u} [Fintype R] [DecidableEq R]
    (Φ : QuantumChannel a b) (Y : Matrix (R × b) (R × b) ℂ) :
    (defectR Φ Y).PosSemidef := by
  rw [amplified_defect]
  have he : (e Φ).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (e Φ)
    rw [e_star Φ, e_mul_self Φ] at h
    exact h
  have h := (amp_pos (R := R) he).conjTranspose_mul_mul_same
    ((piAmp (a := a) Y)ᴴ * amp (R := R) (J Φ))
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc] using h

private lemma amplified_state_bound {R : Type u} [Fintype R] [DecidableEq R]
    (Φ : QuantumChannel a b) (k : ℝ) (σ : DensityState b)
    (W K : Matrix (b × Env a b) a ℂ) (hK : K = J Φ - W)
    (hKflip : ((k : ℂ) • e Φ - K * Kᴴ).PosSemidef)
    (hcompress : ∀ Z : Matrix b b ℂ, (J Φ)ᴴ * pi (a := a) Z * W =
      ((CStarMatrix.ofMatrix.symm σ.1 : Matrix b b ℂ) * Z).trace • (1 : Matrix a a ℂ))
    (Y : Matrix (R × b) (R × b) ℂ) :
    let X := stateCenter σ Y;
      ((k : ℂ) • defectR Φ Y -
        (PhiR Φ Y - Matrix.kronecker X (1 : Matrix a a ℂ)) *
          Matrix.conjTranspose (PhiR Φ Y - Matrix.kronecker X
            (1 : Matrix a a ℂ))).PosSemidef := by
  dsimp only
  let X := stateCenter σ Y
  have hX : PhiR Φ Y - Matrix.kronecker X (1 : Matrix a a ℂ) =
      (amp (R := R) (J Φ))ᴴ * piAmp (a := a) Y * amp (R := R) K := by
    rw [PhiR_factor]
    change _ - stateCenter σ Y ⊗ₖ (1 : Matrix a a ℂ) = _
    rw [← amp_state_compression Φ σ W hcompress Y, hK, amp_sub, Matrix.mul_sub]
  have hflip := amp_supported_flip (R := R) (a := a) Φ K k hKflip
  have hcong := hflip.conjTranspose_mul_mul_same
    ((piAmp (a := a) Y)ᴴ * amp (R := R) (J Φ))
  change ((k : ℂ) • defectR Φ Y -
    (PhiR Φ Y - Matrix.kronecker X (1 : Matrix a a ℂ)) *
      (PhiR Φ Y - Matrix.kronecker X (1 : Matrix a a ℂ))ᴴ).PosSemidef
  rw [hX, amplified_defect]
  convert hcong using 1 <;>
    simp [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]

private lemma stateCenter_star {R : Type u} [Fintype R] [DecidableEq R]
    (σ : DensityState b) (Y : Matrix (R × b) (R × b) ℂ) :
    stateCenter σ Yᴴ = (stateCenter σ Y)ᴴ := by
  have hσ : (CStarMatrix.ofMatrix.symm σ.1 : Matrix b b ℂ).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm σ.nonnegative)).isHermitian
  ext r s
  change ((CStarMatrix.ofMatrix.symm σ.1 : Matrix b b ℂ) *
    Yᴴ.submatrix (fun u => (r,u)) (fun v => (s,v))).trace =
    star (((CStarMatrix.ofMatrix.symm σ.1 : Matrix b b ℂ) *
      Y.submatrix (fun u => (s,u)) (fun v => (r,v))).trace)
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hσ.eq,
    Matrix.trace_mul_comm]
  rfl

/-- One positive trace-one state controls both actual completely amplified
residual Grams at the same weighted ordinary partial-trace center. -/
theorem common_positive_state_scalarizer
    (Φ : QuantumChannel a b) (k : ℝ) (hk : 0 ≤ k)
    (hUniversal : UniversalPositiveTraceTest Φ k) :
    ∃ σ : DensityState b,
      ∀ {R : Type u} [Fintype R] [DecidableEq R]
        (Y : Matrix (R × b) (R × b) ℂ),
        let X := stateCenter σ Y;
        let Δ := PhiR Φ Y - X ⊗ₖ (1 : Matrix a a ℂ);
        X = D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight
          (((1 : Matrix R R ℂ) ⊗ₖ (CStarMatrix.ofMatrix.symm σ.1 : Matrix b b ℂ)) * Y) ∧
        (((k : ℂ) • (PhiR Φ (Y * Yᴴ) - PhiR Φ Y * (PhiR Φ Y)ᴴ)) -
          Δ * Δᴴ).PosSemidef ∧
        (((k : ℂ) • (PhiR Φ (Yᴴ * Y) - (PhiR Φ Y)ᴴ * PhiR Φ Y)) -
          Δᴴ * Δ).PosSemidef := by
  obtain ⟨σ,W,K,hW,heW,hK,hKorth,heK,hKflip,hcompress⟩ :=
    common_positive_state_compression Φ k hk hUniversal
  refine ⟨σ,?_⟩
  intro R _ _ Y
  refine ⟨stateCenter_partialTrace σ Y,
    amplified_state_bound Φ k σ W K hK hKflip hcompress Y, ?_⟩
  have h := amplified_state_bound Φ k σ W K hK hKflip hcompress Yᴴ
  have hΔ : PhiR Φ Yᴴ - stateCenter σ Yᴴ ⊗ₖ (1 : Matrix a a ℂ) =
      (PhiR Φ Y - stateCenter σ Y ⊗ₖ (1 : Matrix a a ℂ))ᴴ := by
    simp only [PhiR_star, stateCenter_star, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  dsimp only at h ⊢
  change (((k : ℂ) • defectR Φ Yᴴ) -
    (PhiR Φ Yᴴ - stateCenter σ Yᴴ ⊗ₖ (1 : Matrix a a ℂ)) *
      (PhiR Φ Yᴴ - stateCenter σ Yᴴ ⊗ₖ (1 : Matrix a a ℂ))ᴴ).PosSemidef at h
  rw [hΔ] at h
  simpa only [defectR, Matrix.conjTranspose_conjTranspose, PhiR_star] using h

#print axioms selected_column_joint_gram
#print axioms common_positive_state_scalarizer

end D5.S3.Quantum.Divergence.UniversalPositiveScalarizer
