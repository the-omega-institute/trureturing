/- GID: D5/S3/Quantum/Divergence/UniversalPositiveScalarizer
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/UniversalPositiveScalarizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual selected-column joint Gram extraction for finite channel adjoints. -/

import D5.S3.Quantum.Divergence.CanonicalRelativeModularModel
import D5.S3.Quantum.Divergence.UniversalCommonCenter
import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

/-! Joint basis-residual Gram control from universal positive trace tests.

The canonical Kraus column supplies the actual adjoint and defect Gram.
A common matrix center has one selected column; all its other columns remain
as a positive Gram remainder.  The original Umegaki coefficient equality and
the later scalarizer, density and reference-amplification steps remain open.

proof_shape: content; admission_basis: escape-witness.
escape_witness: residual_gram_split, consumed by selected_column_joint_gram.
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

private lemma Phi_block (Φ : QuantumChannel a b) {R : Type u}
    [Fintype R] [DecidableEq R] (Y : Matrix (R × b) (R × b) ℂ)
    (r s : R) :
    (fun u v => ∑ c : Env a b, ∑ x : b, ∑ y : b,
      star (K Φ c x u) * Y (r,x) (s,y) * K Φ c y v) =
      Phi Φ (fun x y => Y (r,x) (s,y)) := by
  rfl

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

private lemma PhiR_star (Φ : QuantumChannel a b)
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

private lemma packedY_block (i₀ i j : I b) (x y : b) :
    packedY i₀ (i,x) (j,y) = if j = i₀ then E i x y else 0 := rfl

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

#print axioms selected_column_joint_gram

end D5.S3.Quantum.Divergence.UniversalPositiveScalarizer
