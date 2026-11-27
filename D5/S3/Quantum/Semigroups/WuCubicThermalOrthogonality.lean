/- GID: D5/S3/Quantum/Semigroups/WuCubicThermalOrthogonality
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicThermalOrthogonality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gibbs square-root trace pairing and exact orthogonality of the Wu thermal directions. -/

import D5.S3.Quantum.Semigroups.WuCubicThermalBasis

/-! The Gibbs-symmetric Gram matrix of the physical two-mode Wu basis. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Semigroups.WuCubicThermalOrthogonality

open WuCubicOperatorBridge (D G Mat Occupation)
open WuCubicThermalBasis
open private G_pow_six rootValue rootValue_pos from
  D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
open private gibbsOccupation from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private phase parityValue phase_sq twistedTensor direction_eq_tensor from
  D5.S3.Quantum.Semigroups.WuCubicThermalBasis

/-- The Gibbs-symmetric pairing, conjugate-linear in the first argument. -/
def gibbsPairing (r : ℝ) (X Y : Mat) : ℂ :=
  let S := CFC.sqrt (D r)
  (S * Xᴴ * S * Y).trace

/-- The pairing in the `G` normalization used by the physical Hessian. -/
theorem gibbsPairing_eq_trace_G {r : ℝ} (hr : 1 ≤ r) (X Y : Mat) :
    gibbsPairing r X Y = (G r ^ 3 * Xᴴ * G r ^ 3 * Y).trace := by
  have hS : CFC.sqrt (D r) = G r ^ 3 := by
    apply CFC.sqrt_unique
    · rw [← pow_add]
      exact G_pow_six hr
    · apply Matrix.PosSemidef.nonneg
      rw [G, Matrix.diagonal_pow]
      apply Matrix.posSemidef_diagonal_iff.mpr
      intro i
      change 0 ≤ (rootValue r i : ℂ) ^ 3
      rw [← Complex.ofReal_pow]
      exact Complex.zero_le_real.mpr (pow_nonneg (rootValue_pos hr i).le 3)
  simp only [gibbsPairing, hS]

/-- Squared norms in the local order identity, lowering, raising, population. -/
def localNormSq (r : ℝ) (k : Fin 4) : ℝ :=
  ![1, Real.sqrt (a r * b r), Real.sqrt (a r * b r), a r * b r] k

/-- The squared norm of a two-mode direction is the product of its local weights. -/
def directionNormSq (r : ℝ) (k : Index) : ℝ :=
  localNormSq r k.1 * localNormSq r k.2

private def localRoot (r : ℝ) (i : Fin 2) : ℂ :=
  (Real.sqrt (gibbsOccupation r i) : ℂ)

private theorem occupation_nonneg {r : ℝ} (hr : 0 ≤ r) (i : Fin 2) :
    0 ≤ gibbsOccupation r i := by
  have ha : 0 ≤ a r := by unfold a; positivity
  have hb : 0 ≤ b r := mul_nonneg (pow_nonneg hr 3) ha
  fin_cases i
  · exact ha
  · exact hb

private theorem localRoot_sq {r : ℝ} (hr : 0 ≤ r) (i : Fin 2) :
    localRoot r i * localRoot r i = (gibbsOccupation r i : ℂ) := by
  simp only [localRoot, ← Complex.ofReal_mul, Real.mul_self_sqrt (occupation_nonneg hr i)]

private theorem sqrt_D {r : ℝ} (hr : 0 ≤ r) :
    CFC.sqrt (D r) = diagonal (fun i : Occupation => localRoot r i.1 * localRoot r i.2) := by
  apply CFC.sqrt_unique
  · rw [D, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    calc
      _ = (localRoot r i.1 * localRoot r i.1) * (localRoot r i.2 * localRoot r i.2) := by ring
      _ = _ := by simp only [localRoot_sq hr, Complex.ofReal_mul]
  · apply Matrix.PosSemidef.nonneg
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    simp only [localRoot, ← Complex.ofReal_mul]
    exact Complex.zero_le_real.mpr (mul_nonneg (Real.sqrt_nonneg (gibbsOccupation r i.1))
      (Real.sqrt_nonneg (gibbsOccupation r i.2)))

private def entryPair {n : Type*} (s : n → ℂ) (X Y : Matrix n n ℂ) (i j : n) : ℂ :=
  s i * s j * (conj (X i j) * Y i j)

private theorem gibbsPairing_entries {r : ℝ} (hr : 0 ≤ r) (X Y : Mat) :
    gibbsPairing r X Y =
      ∑ i : Occupation, ∑ j : Occupation,
        entryPair (fun p : Occupation => localRoot r p.1 * localRoot r p.2) X Y i j := by
  rw [gibbsPairing, sqrt_D hr, Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Complex.star_def, entryPair]
  ring

private def localPairing (r : ℝ) (X Y : LocalMat) : ℂ :=
  ∑ i : Fin 2, ∑ j : Fin 2, entryPair (localRoot r) X Y i j

private theorem conj_phase (i j s : Fin 2) : conj (phase i j s) = phase i j s := by
  by_cases h : i = j
  · simp [phase, h]
  · fin_cases s <;> norm_num [phase, h, parityValue]

private theorem gibbsPairing_twistedTensor {r : ℝ} (hr : 0 ≤ r) (X Y U V : LocalMat) :
    gibbsPairing r (twistedTensor X U) (twistedTensor Y V) =
      localPairing r X Y * localPairing r U V := by
  let L := entryPair (localRoot r) X Y
  let R := entryPair (localRoot r) U V
  rw [gibbsPairing_entries hr]
  simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ i : Fin 2, ∑ s : Fin 2, ∑ j : Fin 2, ∑ t : Fin 2, L i j * R s t := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun s _ =>
        Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun t _ => ?_))))
      simp only [entryPair, twistedTensor, map_mul, conj_phase, Prod.fst, Prod.snd]
      calc
        _ = (phase i j s * phase i j s) * (L i j * R s t) := by
          dsimp only [L, R, entryPair]
          ring
        _ = _ := by rw [phase_sq, one_mul]
    _ = ∑ i : Fin 2, ∑ j : Fin 2, ∑ s : Fin 2, ∑ t : Fin 2, L i j * R s t := by
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = _ := by
      simp only [localPairing, Finset.sum_mul]
      simp only [Finset.mul_sum, L, R]

private theorem localPairing_vector {r : ℝ} (hr : 0 ≤ r) (k l : Fin 4) :
    localPairing r (localVector r k) (localVector r l) =
      if k = l then (localNormSq r k : ℂ) else 0 := by
  have hab : (a r : ℂ) + (b r : ℂ) = 1 := by exact_mod_cast a_add_b hr
  have h00 : localRoot r 0 * localRoot r 0 = (a r : ℂ) := localRoot_sq hr 0
  have h11 : localRoot r 1 * localRoot r 1 = (b r : ℂ) := localRoot_sq hr 1
  have h01 : localRoot r 0 * localRoot r 1 = (Real.sqrt (a r * b r) : ℂ) := by
    have ha : 0 ≤ a r := occupation_nonneg hr 0
    change (Real.sqrt (a r) : ℂ) * (Real.sqrt (b r) : ℂ) = _
    rw [← Complex.ofReal_mul, Real.sqrt_mul ha]
  have h10 := (mul_comm (localRoot r 1) (localRoot r 0)).trans h01
  fin_cases k <;> fin_cases l <;>
    norm_num [localPairing, entryPair, Fin.sum_univ_two, localVector, localNormSq, e,
      population, Matrix.one_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul,
      h00, h01, h10, h11, hab] <;>
    first | ring1 | linear_combination ((a r : ℂ) * (b r : ℂ)) * hab

/-- All sixteen physical directions are orthogonal, including at the tracial endpoint. -/
theorem gibbsPairing_direction {r : ℝ} (hr : 0 ≤ r) (k l : Index) :
    gibbsPairing r (direction r k) (direction r l) =
      if k = l then (directionNormSq r k : ℂ) else 0 := by
  obtain ⟨p, q⟩ := k
  obtain ⟨u, v⟩ := l
  simp only [direction_eq_tensor, gibbsPairing_twistedTensor hr, localPairing_vector hr,
    Prod.fst, Prod.snd, Prod.mk.injEq, directionNormSq, Complex.ofReal_mul]
  by_cases hp : p = u <;> by_cases hq : q = v <;> simp [hp, hq]

/-- The same diagonal form in the explicit complex coordinates of arbitrary matrices. -/
theorem gibbsPairing_expansion {r : ℝ} (hr : 0 ≤ r) (X Y : Mat) :
    gibbsPairing r X Y = ∑ k : Index,
      conj (coefficient r X k) * coefficient r Y k * (directionNormSq r k : ℂ) := by
  have hleft (Z : Mat) :
      gibbsPairing r (∑ k : Index, coefficient r X k • direction r k) Z =
        ∑ k : Index, conj (coefficient r X k) * gibbsPairing r (direction r k) Z := by
    simp only [gibbsPairing, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
      Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Complex.star_def]
  have hright (Z : Mat) :
      gibbsPairing r Z (∑ k : Index, coefficient r Y k • direction r k) =
        ∑ k : Index, coefficient r Y k * gibbsPairing r Z (direction r k) := by
    simp only [gibbsPairing, Finset.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
      Matrix.trace_smul, smul_eq_mul]
  conv_lhs => rw [← expansion hr X, ← expansion hr Y]
  rw [hleft]
  simp only [hright, Finset.mul_sum, gibbsPairing_direction hr]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_eq_single k]
  · simp [mul_assoc]
  · intro l _ hl
    simp [Ne.symm hl]
  · simp

end D5.S3.Quantum.Semigroups.WuCubicThermalOrthogonality
