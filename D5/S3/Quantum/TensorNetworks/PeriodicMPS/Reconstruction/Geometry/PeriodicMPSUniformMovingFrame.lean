/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrame
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformMovingFrame
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Moving frames for the periodic mixed transfer. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.UniformNativeCriticalMatrix
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection.PeriodicMPSExchangeSymmetry
import Mathlib.LinearAlgebra.Matrix.DualNumber
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame

open Matrix MvPolynomial TrivSqZeroExt
open scoped Matrix Kronecker
open PeriodicMPSUniformAntisymmetricTransfer (BondMatrix TransferMatrix mixedRaw mixedTransfer)
open PeriodicMPSUniformHardCoreTransferRecurrence (TwoBits binaryInsertion binaryTransfer)
open SevenSiteCriticalCertificate (observedRow rotationIndex sliceBlock)
open PeriodicMPSUniformNativeSliceReadout
  (alignedMoment pauliInsertion rawSlicePolynomial alignedMoment_eq_transferPower)
open UniformNativeRotation (rotationPolynomial)
open UniformNativeCriticalMatrix (criticalMatrix)

open private pauli map_pauli from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalCertificate
open private map_alignedWord trace_pauli_mul_mixedRaw from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.UniformNativeSliceReadout

noncomputable section

abbrev Core (R : Type*) := Fin 2 → BondMatrix R

variable {R : Type*} [CommRing R]

/-- Physical mixing acts on the family index, leaving the bond indices fixed. -/
def mix (g : BondMatrix R) (A : Core R) : Core R :=
  fun i => ∑ j, g i j • A j

theorem mix_mul (g h : BondMatrix R) (A : Core R) :
    mix (g * h) A = mix g (mix h A) := by
  funext i
  simp only [mix, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

/-- The contragredient physical action preserves the mixed transfer itself. -/
theorem mixedTransfer_mix (g h : BondMatrix R) (hg : h * g = 1)
    (A B : Core R) :
    mixedTransfer (mix g A) (mix hᵀ B) = mixedTransfer A B := by
  have coeff (i j : Fin 2) : h i 0 * g 0 j + h i 1 * g 1 j = (1 : BondMatrix R) i j := by
    have eq := congrFun (congrFun hg i) j
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using eq
  ext i j
  simp only [mixedTransfer, binaryTransfer, mix, Fin.sum_univ_two, Matrix.transpose_apply,
    Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
  have c00 := coeff 0 0
  have c01 := coeff 0 1
  have c10 := coeff 1 0
  have c11 := coeff 1 1
  simp at c00 c01 c10 c11
  calc
    _ = (h 0 0 * g 0 0 + h 0 1 * g 1 0) * (B 0 i.1 j.1 * A 0 i.2 j.2) +
        (h 0 0 * g 0 1 + h 0 1 * g 1 1) * (B 0 i.1 j.1 * A 1 i.2 j.2) +
        (h 1 0 * g 0 0 + h 1 1 * g 1 0) * (B 1 i.1 j.1 * A 0 i.2 j.2) +
        (h 1 0 * g 0 1 + h 1 1 * g 1 1) * (B 1 i.1 j.1 * A 1 i.2 j.2) := by ring
    _ = _ := by simp [c00, c01, c10, c11]

def pairFrame (g : BondMatrix R) : TransferMatrix R := g ⊗ₖ g

private theorem insertion_mix (g h : BondMatrix R) (A B : Core R) (p q : TwoBits) :
    binaryInsertion (mix hᵀ B) (mix g A) q p =
      ∑ v : TwoBits, ∑ w : TwoBits,
        (pairFrame g p v * pairFrame h w q) • binaryInsertion B A w v := by
  have words (f : BondMatrix R) (D : Core R) (s : TwoBits) :
      mix f D s.1 * mix f D s.2 = ∑ v : TwoBits, pairFrame f s v • (D v.1 * D v.2) := by
    simp only [mix, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
      Fintype.sum_prod_type, pairFrame, Matrix.kroneckerMap_apply]
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  unfold binaryInsertion
  rw [words, words]
  let K : BondMatrix R →ₗ[R] BondMatrix R →ₗ[R] TransferMatrix R :=
    Matrix.kroneckerBilinear
  change K _ _ = ∑ v : TwoBits, ∑ w : TwoBits, _ • K _ _
  simp only [map_sum, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.map_smul, smul_smul]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  rw [mul_comm]
  rfl

/-- The raw observation has the two-site GL₂ action over every commutative
ring, including the dual-number ring and reducible cores. -/
theorem mixedRaw_mix (g h : BondMatrix R) (hg : h * g = 1)
    (A B : Core R) (m : ℕ) :
    mixedRaw (mix g A) (mix hᵀ B) m =
      pairFrame g * mixedRaw A B m * pairFrame h := by
  ext p q
  simp only [mixedRaw, insertion_mix, mixedTransfer_mix g h hg, Matrix.trace_sum,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem pairFrame_mul (g h : BondMatrix R) :
    pairFrame (g * h) = pairFrame g * pairFrame h :=
  Matrix.mul_kronecker_mul _ _ _ _

@[simp] theorem pairFrame_one : pairFrame (1 : BondMatrix R) = 1 :=
  Matrix.one_kronecker_one

/-- An explicit inverse for the trace-aligning frame. -/
def traceFrame (a b : Fin 2 → R) : BondMatrix R :=
  !![b 0, b 1; a 1, -a 0]

def traceFrameInverse (a b : Fin 2 → R) : BondMatrix R :=
  !![a 0, b 1; a 1, -b 0]

theorem traceFrame_inverse (a b : Fin 2 → R) (hab : a 0 * b 0 + a 1 * b 1 = 1) :
    traceFrameInverse a b * traceFrame a b = 1 ∧
      traceFrame a b * traceFrameInverse a b = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [traceFrame, traceFrameInverse, Matrix.mul_apply, Fin.sum_univ_two,
      ← hab, mul_comm] <;> ring

def traces (A : Core R) : Fin 2 → R := fun i => (A i).trace

theorem traceFrame_aligns (A B : Core R)
    (hab : traces A 0 * traces B 0 + traces A 1 * traces B 1 = 1) :
    traces (mix (traceFrame (traces A) (traces B)) A) = ![1, 0] ∧
      traces (mix (traceFrameInverse (traces A) (traces B))ᵀ B) = ![1, 0] := by
  constructor <;> funext i <;> fin_cases i <;>
    simp [traces, mix, traceFrame, traceFrameInverse, Fin.sum_univ_two, Matrix.trace_add,
      Matrix.trace_smul, ← hab, mul_comm]

variable {E : Type*} [Field E]

local notation "D" => DualNumber E

def jetValue {n : Type*} (M : Matrix n n D) : Matrix n n E := M.map fst
def jetTangent {n : Type*} (M : Matrix n n D) : Matrix n n E := M.map snd

private theorem value_mul {n : Type*} [Fintype n] (M N : Matrix n n D) :
    jetValue (M * N) = jetValue M * jetValue N := by
  ext i j
  simp [jetValue, Matrix.mul_apply, fst_sum]

private theorem tangent_mul {n : Type*} [Fintype n] (M N : Matrix n n D) :
    jetTangent (M * N) = jetValue M * jetTangent N + jetTangent M * jetValue N := by
  ext i j
  simp [jetTangent, jetValue, Matrix.mul_apply, snd_sum,
    Finset.sum_add_distrib]

private theorem jetValue_pairFrame (g : BondMatrix D) :
    jetValue (pairFrame g) = pairFrame (jetValue g) := rfl

def pairGenerator (H : BondMatrix E) : TransferMatrix E :=
  H ⊗ₖ (1 : BondMatrix E) + (1 : BondMatrix E) ⊗ₖ H

def physicalTangent (H : BondMatrix E) (W : TransferMatrix E) : TransferMatrix E :=
  pairGenerator H * W - W * pairGenerator H

private theorem tangent_pairFrame_mul (g h : BondMatrix D) (hgh : g * h = 1) :
    jetTangent (pairFrame g) * pairFrame (jetValue h) =
      pairGenerator (jetTangent g * jetValue h) := by
  have h₀ : jetValue g * jetValue h = 1 := by
    rw [← value_mul, hgh]
    ext i j
    by_cases h : i = j <;> simp [jetValue, Matrix.one_apply, h]
  have hp : jetTangent (pairFrame g) =
      jetTangent g ⊗ₖ jetValue g + jetValue g ⊗ₖ jetTangent g := by
    ext i j
    simp [jetTangent, jetValue, pairFrame, Matrix.kroneckerMap_apply,
      add_comm]
  rw [hp, add_mul, pairFrame, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, h₀]
  rfl

/-- Differentiate the physical conjugation. The generator is the
right logarithmic derivative of the moving physical frame. -/
theorem mixedRaw_movingFrame_jet (g h : BondMatrix D)
    (hhg : h * g = 1) (hgh : g * h = 1) (A B : Core D) (m : ℕ) :
    let V := mixedRaw (mix g A) (mix hᵀ B) m
    pairFrame (jetValue g) * jetTangent (mixedRaw A B m) * pairFrame (jetValue h) =
      jetTangent V - physicalTangent (jetTangent g * jetValue h) (jetValue V) := by
  dsimp only
  let W := mixedRaw A B m
  let G := pairFrame g
  let J := pairFrame h
  let H := pairGenerator (jetTangent g * jetValue h)
  have hGJ : G * J = 1 := by rw [← pairFrame_mul, hgh, pairFrame_one]
  have hJG : J * G = 1 := by rw [← pairFrame_mul, hhg, pairFrame_one]
  have e₀ : jetValue G * jetValue J = 1 := by
    rw [← value_mul, hGJ]
    ext i j
    by_cases h : i = j <;> simp [jetValue, Matrix.one_apply, h]
  have e₁ : jetValue J * jetValue G = 1 := by
    rw [← value_mul, hJG]
    ext i j
    by_cases h : i = j <;> simp [jetValue, Matrix.one_apply, h]
  have e₂ : jetTangent G * jetValue J = H := tangent_pairFrame_mul g h hgh
  have e₃ : jetValue G * jetTangent J + jetTangent G * jetValue J = 0 := by
    rw [← tangent_mul, hGJ]
    ext i j
    by_cases h : i = j <;> simp [jetTangent, h]
  have e₄ : jetTangent J = -(jetValue J * H) := by
    rw [e₂] at e₃
    have he := congrArg (jetValue J * ·) e₃
    rw [mul_add, ← mul_assoc, e₁, one_mul, mul_zero] at he
    exact eq_neg_of_add_eq_zero_left he
  have e₅ : jetTangent G = H * jetValue G := by
    rw [← e₂, mul_assoc, e₁, mul_one]
  rw [mixedRaw_mix g h hhg]
  change jetValue G * jetTangent W * jetValue J =
    jetTangent (G * W * J) - (H * jetValue (G * W * J) - jetValue (G * W * J) * H)
  simp only [tangent_mul, value_mul]
  rw [e₄, e₅, add_mul, mul_neg]
  simp only [mul_assoc]
  abel

/-- The value part transforms by the constant frame, including the raw radial
column of the augmented matrix. -/
theorem mixedRaw_movingFrame_radial (g h : BondMatrix D)
    (hhg : h * g = 1) (A B : Core D) (m : ℕ) :
    jetValue (mixedRaw (mix g A) (mix hᵀ B) m) =
      pairFrame (jetValue g) * jetValue (mixedRaw A B m) * pairFrame (jetValue h) := by
  rw [mixedRaw_mix g h hhg, value_mul, value_mul, jetValue_pairFrame, jetValue_pairFrame]

def mixedTrace (A : Core R) : R := (A 0 * A 1).trace

def balance (t : R) : BondMatrix R := !![1, 0; 0, t]

private theorem balance_mix (t : R) (A : Core R) :
    mix (balance t) A 0 = A 0 ∧ mix (balance t) A 1 = t • A 1 := by
  simp [mix, balance, Fin.sum_univ_two]

private theorem balance_inverse {t v : R} (h : t * v = 1) :
    balance t * balance v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [balance, Matrix.mul_apply, Fin.sum_univ_two, h]

variable [CharZero E]

/-- A nonzero square root extends to the aligned dual-number jet by the
explicit first-order separable lift. -/
theorem lift_balancing_root (kA kB : D) (τ : E) (hA : kA.fst ≠ 0) (ht : τ ≠ 0)
    (hτ : τ ^ 2 * kA.fst = kB.fst) :
    ∃ t v : D, t.fst = τ ∧ t * v = 1 ∧ t ^ 2 * kA = kB := by
  have htwo : (2 : E) ≠ 0 := two_ne_zero
  let d := (kB.snd - τ ^ 2 * kA.snd) / (2 * τ * kA.fst)
  have hd : d * (2 * τ * kA.fst) = kB.snd - τ ^ 2 * kA.snd :=
    div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero htwo ht) hA)
  let t : D := ⟨τ, d⟩
  refine ⟨t, ⟨τ⁻¹, -d / τ ^ 2⟩, rfl, ?_, ?_⟩
  · apply TrivSqZeroExt.ext
    · change τ * τ⁻¹ = 1
      exact mul_inv_cancel₀ ht
    · change τ * (-d / τ ^ 2) + d * τ⁻¹ = 0
      field_simp
      ring
  · apply TrivSqZeroExt.ext
    · rw [pow_two]
      change τ * τ * kA.fst = kB.fst
      simpa only [pow_two] using hτ
    · rw [pow_two]
      change τ * τ * kA.snd + (τ * d + d * τ) * kA.fst = kB.snd
      linear_combination hd

/-- Assemble the trace alignment and the diagonal balancing in the dual
ring. Both resulting mixed traces agree as dual numbers. -/
theorem exists_balancedFrame_fixedValue (A B : Core D)
    (hab : traces A 0 * traces B 0 + traces A 1 * traces B 1 = 1)
    (τ : E)
    (hA : (mixedTrace (mix (traceFrame (traces A) (traces B)) A)).fst ≠ 0)
    (ht : τ ≠ 0)
    (hτ : τ ^ 2 * (mixedTrace (mix (traceFrame (traces A) (traces B)) A)).fst =
      (mixedTrace (mix (traceFrameInverse (traces A) (traces B))ᵀ B)).fst) :
    ∃ g h : BondMatrix D, h * g = 1 ∧ g * h = 1 ∧
      traces (mix g A) = ![1, 0] ∧ traces (mix hᵀ B) = ![1, 0] ∧
      mixedTrace (mix g A) = mixedTrace (mix hᵀ B) ∧
      jetValue g = balance τ * traceFrame (fun i => (traces A i).fst) (fun i => (traces B i).fst) ∧
      jetValue h = traceFrameInverse (fun i => (traces A i).fst) (fun i => (traces B i).fst) *
        balance τ⁻¹ := by
  let f := traceFrame (traces A) (traces B)
  let j := traceFrameInverse (traces A) (traces B)
  obtain ⟨t, v, ht₀, ht₁, ht₂⟩ := lift_balancing_root
    (mixedTrace (mix f A)) (mixedTrace (mix jᵀ B)) τ hA ht hτ
  obtain ⟨hjf, hfj⟩ := traceFrame_inverse (traces A) (traces B) hab
  obtain ⟨hA', hB'⟩ := traceFrame_aligns A B hab
  have hv := balance_inverse (mul_comm t v ▸ ht₁)
  have ht' := balance_inverse ht₁
  have hbtr (w : D) (C : Core D) (hc : traces C = ![1, 0]) :
      traces (mix (balance w) C) = ![1, 0] := by
    funext i
    fin_cases i
    · exact (congrArg Matrix.trace (balance_mix w C).1).trans (congrFun hc 0)
    · change (mix (balance w) C 1).trace = 0
      rw [(balance_mix w C).2, Matrix.trace_smul]
      have h0 : (C 1).trace = 0 := congrFun hc 1
      simp [h0]
  have hbt (w : D) (C : Core D) :
      mixedTrace (mix (balance w) C) = w * mixedTrace C := by
    rw [mixedTrace, (balance_mix w C).1, (balance_mix w C).2]
    change (C 0 * w • C 1).trace = w * (C 0 * C 1).trace
    rw [Matrix.mul_smul (C 0) w (C 1), Matrix.trace_smul]
    rfl
  have htrans : (balance v)ᵀ = balance v := by
    apply Matrix.ext
    intro i k
    fin_cases i <;> fin_cases k <;> rfl
  have hv₀ : v.fst = τ⁻¹ := by
    have h := congrArg fst ht₁
    change t.fst * v.fst = 1 at h
    rw [ht₀, mul_comm] at h
    exact eq_inv_of_mul_eq_one_left h
  have hl (w : D) : jetValue (balance w) = balance w.fst := by
    apply Matrix.ext
    intro i k
    fin_cases i <;> fin_cases k <;> rfl
  have hf : jetValue f =
      traceFrame (fun i => (traces A i).fst) (fun i => (traces B i).fst) := by
    apply Matrix.ext
    intro i k
    fin_cases i <;> fin_cases k <;> rfl
  have hj : jetValue j =
      traceFrameInverse (fun i => (traces A i).fst) (fun i => (traces B i).fst) := by
    apply Matrix.ext
    intro i k
    fin_cases i <;> fin_cases k <;> rfl
  refine ⟨balance t * f, j * balance v, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mul_assoc, ← mul_assoc (balance v), hv, one_mul, hjf]
  · rw [mul_assoc, ← mul_assoc f, hfj, one_mul, ht']
  · rw [mix_mul]
    exact hbtr t _ hA'
  · rw [Matrix.transpose_mul, htrans, mix_mul]
    exact hbtr v _ hB'
  · rw [Matrix.transpose_mul, htrans, mix_mul, mix_mul, hbt, hbt, ← ht₂, pow_two]
    calc
      _ = (t * v) * t * mixedTrace (mix f A) := by rw [ht₁, one_mul]
      _ = _ := by ring
  · rw [value_mul, hl, ht₀, hf]
  · rw [value_mul, hj, hl, hv₀]

theorem exists_balancedFrame (A B : Core D)
    (hab : traces A 0 * traces B 0 + traces A 1 * traces B 1 = 1)
    (τ : E)
    (hA : (mixedTrace (mix (traceFrame (traces A) (traces B)) A)).fst ≠ 0)
    (ht : τ ≠ 0)
    (hτ : τ ^ 2 * (mixedTrace (mix (traceFrame (traces A) (traces B)) A)).fst =
      (mixedTrace (mix (traceFrameInverse (traces A) (traces B))ᵀ B)).fst) :
    ∃ g h : BondMatrix D, h * g = 1 ∧ g * h = 1 ∧
      traces (mix g A) = ![1, 0] ∧ traces (mix hᵀ B) = ![1, 0] ∧
      mixedTrace (mix g A) = mixedTrace (mix hᵀ B) := by
  obtain ⟨g, h, hhg, hgh, ha, hb, hk, _, _⟩ :=
    exists_balancedFrame_fixedValue A B hab τ hA ht hτ
  exact ⟨g, h, hhg, hgh, ha, hb, hk⟩

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformMovingFrame
