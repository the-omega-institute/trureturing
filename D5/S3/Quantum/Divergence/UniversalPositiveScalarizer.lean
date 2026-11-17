import D5.S3.Quantum.Divergence.CanonicalRelativeModularModel
import D5.S3.Quantum.Divergence.UniversalCommonCenter
import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

/-! Working actual consumer for the universal positive-scalarizer route.

The construction is intentionally private and checkpoint oriented.  It starts
from the canonical normalized Kraus family of the channel, forms the actual
trace adjoint on every finite reference, and feeds the packed basis input to
the existing common-center theorem.  The selected-column Gram extraction is
left as the next mathematical gap; no assumed factor or state identity is
introduced here.
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

private abbrev Env (a b : Type*) [Fintype a] [Fintype b] :=
  Fin (Fintype.card b) × Fin (Fintype.card a)

private abbrev K (Φ : QuantumChannel a b) : Env a b → Matrix b a ℂ :=
  (actual_kraus_representation Φ).kraus

/-- The actual Stinespring column, with output index first as required by the
canonical Kraus convention. -/
private def J (Φ : QuantumChannel a b) : Matrix (b × Env a b) a ℂ :=
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
private def Phi (Φ : QuantumChannel a b) (Y : Matrix b b ℂ) : Matrix a a ℂ :=
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
private def PhiR (Φ : QuantumChannel a b) {R : Type u}
    [Fintype R] [DecidableEq R] (Y : Matrix (R × b) (R × b) ℂ) :
    Matrix (R × a) (R × a) ℂ :=
  fun (r,x) (s,y) => Phi Φ (fun u v => Y (r,u) (s,v)) x y

private def defectR (Φ : QuantumChannel a b) {R : Type u}
    [Fintype R] [DecidableEq R] (Y : Matrix (R × b) (R × b) ℂ) :
    Matrix (R × a) (R × a) ℂ :=
  PhiR Φ (Y * Yᴴ) - PhiR Φ Y * (PhiR Φ Y)ᴴ

private abbrev I (b : Type*) := b × b

private def E (i : I b) : Matrix b b ℂ := Matrix.single i.1 i.2 1

private def packedY (i₀ : I b) : Matrix (I b × b) (I b × b) ℂ :=
  fun (i,x) (j,y) => if j = i₀ then E i x y else 0

private lemma packedY_block (i₀ i j : I b) (x y : b) :
    packedY i₀ (i,x) (j,y) = if j = i₀ then E i x y else 0 := rfl

private lemma packed_Phi_block (Φ : QuantumChannel a b)
    (i₀ i j : I b) (x y : a) :
    PhiR Φ (packedY i₀) (i,x) (j,y) =
      if j = i₀ then Phi Φ (E i) x y else 0 := by
  classical
  by_cases h : j = i₀
  · simp [PhiR, Phi, packedY, E, h]
  · simp [PhiR, Phi, packedY, h]

/-- The original universal trace-inf premise, expressed on the actual
amplified trace adjoint. -/
private def UniversalPositiveTraceTest (Φ : QuantumChannel a b) (k : ℝ) : Prop :=
  ∀ {R : Type u} [Fintype R] [DecidableEq R]
    (Y : Matrix (R × b) (R × b) ℂ)
    (Z : Matrix (R × a) (R × a) ℂ), Z.PosDef →
    sInf (Set.range (fun X : Matrix R R ℂ =>
      (Z * ((PhiR Φ Y - Matrix.kronecker X (1 : Matrix a a ℂ)) *
        Matrix.conjTranspose (PhiR Φ Y - Matrix.kronecker X (1 : Matrix a a ℂ)))).trace.re)) ≤
      (Z * ((k : ℂ) • defectR Φ Y)).trace.re

/-- First actual consumer: the universal test at the packed one-column basis
input yields a genuine common center for that actual channel.  The extra
Hermitian premise is the explicit remaining transport obligation for the
joint Gram step; it is not an assumed representation or state identity. -/
private lemma packed_common_center
    (Φ : QuantumChannel a b) (k : ℝ) (hk : 0 ≤ k) (i₀ : I b)
    (hB : ((k : ℂ) • defectR Φ (packedY i₀)).IsHermitian)
    (hUniversal : UniversalPositiveTraceTest Φ k) :
    ∃ X : Matrix (I b) (I b) ℂ,
      (((k : ℂ) • defectR Φ (packedY i₀)) -
        (PhiR Φ (packedY i₀) - Matrix.kronecker X (1 : Matrix a a ℂ)) *
          Matrix.conjTranspose (PhiR Φ (packedY i₀) -
            Matrix.kronecker X (1 : Matrix a a ℂ))).PosSemidef := by
  let A := PhiR Φ (packedY i₀)
  let B := (k : ℂ) • defectR Φ (packedY i₀)
  obtain ⟨X, hX⟩ := exists_common_center_of_posDef_trace_inf_le A B hB (by
    intro Z hZ
    exact hUniversal (R := I b) (packedY i₀) Z hZ)
  exact ⟨X, hX⟩

end D5.S3.Quantum.Divergence.UniversalPositiveScalarizer
