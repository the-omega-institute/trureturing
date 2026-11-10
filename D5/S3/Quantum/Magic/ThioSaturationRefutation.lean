/- GID: D5/S3/Quantum/Magic/ThioSaturationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/ThioSaturationRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Magic/ThioSaturationRefutation.claim; result=D5/S3/Quantum/Magic/ThioSaturationRefutation.result; claim=D5/S3/Quantum/Magic/ThioSaturationRefutation.claim
   digest: A noisy Strange qutrit saturates the purity bound with eight Wigner coordinates. -/

import D5.S3.Quantum.Algebra.WeylDisplacementTrace
import D5.S3.Quantum.Algebra.WeylPhaseArithmetic
import D5.S3.Entropy.EntropyEquality
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Saturation outside dimension-multiple coordinate supports -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Matrix ComplexOrder
open D5.S3.Observer.WindowRegister
open D5.S3.Quantum.Algebra.WeylDisplacement
open D5.S3.Entropy.MaxEntropy

namespace D5.S3.Quantum.Magic.ThioSaturationRefutation

/-- The phase-adjusted displacement in the source convention, Eq. (19). -/
def grossDisplacement (q : ℕ) [NeZero q] (a b : ZMod q) : Matrix (ZMod q) (ZMod q) ℂ :=
  windowRoot q ^ (a * b * (((q + 1) / 2 : ℕ) : ZMod q)).val • displacement q a b

/-- The source's sum, including its factor `1/q²`. -/
def grossOrigin (q : ℕ) [NeZero q] : Matrix (ZMod q) (ZMod q) ℂ :=
  ((q : ℂ) ^ 2)⁻¹ • ∑ a, ∑ b, grossDisplacement q a b

/-- Local source phase-space operators; dagger means complex conjugate transpose. -/
def grossLocal (q : ℕ) [NeZero q] (a b : ZMod q) : Matrix (ZMod q) (ZMod q) ℂ :=
  grossDisplacement q a b * grossOrigin q * (grossDisplacement q a b)ᴴ

/-- Tensor product over the local odd dimensions, written on the dependent product basis. -/
def grossTensor (n : ℕ) (q : Fin n → ℕ) (hq : ∀ k, NeZero (q k))
    (a b i j : (k : Fin n) → ZMod (q k)) : ℂ :=
  ∏ k, @grossLocal (q k) (hq k) (a k) (b k) (i k) (j k)

/-- Rank-one projector of a column of a complex orthonormal basis matrix. -/
def columnProjector {I : Type} (U : Matrix I I ℂ) (a : I) : Matrix I I ℂ :=
  Matrix.vecMulVec (fun i => U i a) (fun j => star (U j a))

/-- Source MUB-KD frames, Eq. (17), with both complete bases and all overlaps. -/
def IsMUBKD {I L : Type} [Fintype I] [DecidableEq I]
    (S : L → Matrix I I ℂ) : Prop :=
  ∃ A B : Matrix I I ℂ, Aᴴ * A = 1 ∧ Bᴴ * B = 1 ∧
    (∀ a b, Complex.normSq (∑ i, star (A i a) * B i b) = (Fintype.card I : ℝ)⁻¹) ∧
    ∃ labels : L ≃ I × I, ∀ l,
      S l = columnProjector A (labels l).1 * columnProjector B (labels l).2

/-- Exact odd-local Gross tensor frames, allowing relabeling and an arbitrary orthonormal
computational basis. The dual operators are `card I • S l` as in Eq. (20). -/
def IsGross {I L : Type} [Fintype I] [DecidableEq I]
    (S : L → Matrix I I ℂ) : Prop :=
  ∃ q : ℕ, 0 < q ∧ Odd q ∧ ∃ hq : NeZero q,
    ∃ n : ℕ, 0 < n ∧ ∃ basis : I ≃ (Fin n → ZMod q),
    ∃ labels : L ≃ ((Fin n → ZMod q) × (Fin n → ZMod q)),
    ∃ U : Matrix I I ℂ, Uᴴ * U = 1 ∧ ∀ l,
      S l = U * (show Matrix I I ℂ from fun i j =>
        grossTensor n (fun _ => q) (fun _ => hq)
          (labels l).1 (labels l).2 (basis i) (basis j)) * Uᴴ

/-- The union of the two source classes, without an arbitrary-frame replacement. -/
def IsSourceFrame {I L : Type} [Fintype I] [DecidableEq I]
    (S : L → Matrix I I ℂ) : Prop := IsMUBKD S ∨ IsGross S

/-- Eq. (9), before taking a real part. -/
def coordinate {I : Type} [Fintype I] (rho S : Matrix I I ℂ) : ℂ :=
  Matrix.trace (rho * Sᴴ)

/-- Coordinate support counts nonzero coordinates, rather than matrix rank. -/
def coordinateSupport {L : Type} [Fintype L] (Q : L → ℂ) : ℕ :=
  (Finset.univ.filter fun l => Q l ≠ 0).card

/-- Natural-log Shannon entropy, with `negMulLog 0 = 0`; no coordinate is discarded. -/
def coordinateEntropy {L : Type} [Fintype L] (Q : L → ℂ) : ℝ :=
  shannonEntropy fun l => (Q l).re

/-- The unchanged universal only-multiples saturation assertion. Purity includes both
endpoints. Q positivity includes zero and also asserts that the complex law is real. -/
def claim : Prop :=
  ∀ (I L : Type) [Fintype I] [DecidableEq I] [Fintype L],
    0 < Fintype.card I → ∀ (S : L → Matrix I I ℂ), IsSourceFrame S →
    ∀ rho : Matrix I I ℂ, rho.PosSemidef → Matrix.trace rho = 1 →
    let Q := fun l => coordinate rho (S l)
    let tau := (Matrix.trace (rho * rho)).re
    (∀ l, (Q l).im = 0 ∧ 0 ≤ (Q l).re) →
    (Fintype.card I : ℝ)⁻¹ ≤ tau → tau ≤ 1 →
    coordinateEntropy Q = -Real.log tau + Real.log (Fintype.card I) →
    ∃ delta : ℕ, 1 ≤ delta ∧ delta ≤ Fintype.card I ∧
      coordinateSupport Q = delta * Fintype.card I

/-- The known noisy Strange state, on the source residue basis. -/
def rho : Matrix (ZMod 3) (ZMod 3) ℂ :=
  !![1/4, 0, 0; 0, 3/8, -1/8; 0, -1/8, 3/8]

private theorem root_cube : windowRoot 3 ^ 3 = 1 :=
  (windowRoot_isPrimitiveRoot 3).pow_eq_one

private theorem root_sum : 1 + windowRoot 3 + windowRoot 3 ^ 2 = 0 := by
  have h := (windowRoot_isPrimitiveRoot 3).geom_sum_eq_zero (by norm_num : 1 < 3)
  simpa [Finset.sum_range_succ, pow_zero, pow_one, add_assoc] using h

private theorem root_star : star (windowRoot 3) = windowRoot 3 ^ 2 := by
  have hn := (windowRoot_isPrimitiveRoot 3).norm'_eq_one (by norm_num : 3 ≠ 0)
  have hm : star (windowRoot 3) * windowRoot 3 = 1 := by
    simpa [hn] using RCLike.conj_mul (windowRoot 3)
  have hc : windowRoot 3 ^ 2 * windowRoot 3 = 1 := by
    simpa [pow_succ] using root_cube
  exact mul_right_cancel₀ ((windowRoot_isPrimitiveRoot 3).ne_zero (by norm_num)) (hm.trans hc.symm)

private theorem sum_three {A : Type*} [AddCommMonoid A] (f : ZMod 3 → A) :
    ∑ i, f i = f 0 + f 1 + f 2 := by
  exact Fin.sum_univ_three f

private theorem origin_qutrit : grossOrigin 3 =
    (1 / 3 : ℂ) • (!![1, 0, 0; 0, 0, 1; 0, 1, 0] : Matrix (ZMod 3) (ZMod 3) ℂ) := by
  have h20 : (2 : ZMod 3) ≠ 0 := by decide
  have h21 : (2 : ZMod 3) ≠ 1 := by decide
  have hn1 : (-1 : ZMod 3) = 2 := by decide
  have hn2 : (-2 : ZMod 3) = 1 := by decide
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [h20, h21, Ne.symm h20, Ne.symm h21, hn1, hn2, ZMod, Fin.ext_iff, Fin.neg_def, grossOrigin, grossDisplacement, displacement, shiftMatrix, clockMatrix,
    Matrix.circulant_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply,
    Matrix.add_apply, Pi.add_apply, Fin.val_ofNat,
    pow_two, sum_three, Matrix.smul_apply, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul, ZMod.val_natCast, ZMod.val_ofNat, ZMod.val_zero, ZMod.val_one]
  all_goals try simp +decide only [↓reduceIte, Ne.symm h20, Ne.symm h21]
  all_goals ring_nf
  all_goals try simp only [root_cube,
    ← D5.S3.Quantum.Algebra.WeylPhaseArithmetic.windowRoot_pow_mod (M := 3) 4,
    ← D5.S3.Quantum.Algebra.WeylPhaseArithmetic.windowRoot_pow_mod (M := 3) 5,
    ← D5.S3.Quantum.Algebra.WeylPhaseArithmetic.windowRoot_pow_mod (M := 3) 6]
  all_goals norm_num [h20, h21, Ne.symm h20, Ne.symm h21, hn1, hn2, ZMod, Fin.ext_iff, Fin.neg_def, map_ofNat]
  all_goals try simp +decide only [↓reduceIte, Ne.symm h20, Ne.symm h21]
  all_goals first | linear_combination (1 / 9 : ℂ) * root_sum | linear_combination root_sum

private theorem rho_density : rho.PosSemidef ∧ Matrix.trace rho = 1 := by
  let v : ZMod 3 → ℂ := ![0, 1, -1]
  have hg : rho = (1 / 4 : ℝ) • (1 : Matrix (ZMod 3) (ZMod 3) ℂ) +
      (1 / 8 : ℝ) • Matrix.vecMulVec v (star v) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rho, v, Matrix.vecMulVec, Matrix.one_apply, Matrix.add_apply,
        Pi.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_⟩
  · rw [hg]
    exact (Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1 / 4)).add
      ((Matrix.posSemidef_vecMulVec_self_star v).smul (by norm_num : (0 : ℝ) ≤ 1 / 8))
  · norm_num [rho, Matrix.trace, Matrix.diag_apply, sum_three]

private theorem rho_purity : Matrix.trace (rho * rho) = (3 / 8 : ℂ) := by
  norm_num [rho, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, sum_three,
    Fin.sum_univ_succ]

private def singleEquiv : ZMod 3 ≃ (Fin 1 → ZMod 3) where
  toFun i := fun _ => i
  invFun f := f 0
  left_inv _ := rfl
  right_inv f := by funext k; fin_cases k; rfl

private theorem qutrit_frame_allowed :
    IsSourceFrame (fun p : ZMod 3 × ZMod 3 => grossLocal 3 p.1 p.2) := by
  apply Or.inr
  refine ⟨3, by norm_num, by decide, inferInstance, 1, by norm_num,
    singleEquiv, singleEquiv.prodCongr singleEquiv, 1, by simp, ?_⟩
  intro p
  simp [grossTensor, singleEquiv]

private def law (p : ZMod 3 × ZMod 3) : ℂ := if p = (0, 0) then 0 else 1 / 8

set_option maxHeartbeats 2000000 in
-- The nine identities expand matrix products over three residue indices.
private theorem qutrit_coordinates (p : ZMod 3 × ZMod 3) :
    coordinate rho (grossLocal 3 p.1 p.2) = law p := by
  have h20 : (2 : ZMod 3) ≠ 0 := by decide
  have h21 : (2 : ZMod 3) ≠ 1 := by decide
  have hn1 : (-1 : ZMod 3) = 2 := by decide
  have hn2 : (-2 : ZMod 3) = 1 := by decide
  obtain ⟨a, b⟩ := p
  fin_cases a <;> fin_cases b
  all_goals norm_num [coordinate, grossLocal, origin_qutrit, grossDisplacement,
    displacement, shiftMatrix, clockMatrix, rho, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
    Matrix.circulant_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.add_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_three, Fin.sum_univ_succ,
    ZMod.val_natCast, ZMod.val_ofNat, ZMod.val_zero, ZMod.val_one, pow_two,
    root_star, law, h20, h21, hn1, hn2, ZMod, Fin.ext_iff, Fin.neg_def, map_ofNat]
  all_goals try simp +decide only [↓reduceIte, Ne.symm h20, Ne.symm h21]
  all_goals ring_nf
  all_goals try simp only [
    ← D5.S3.Quantum.Algebra.WeylPhaseArithmetic.windowRoot_pow_mod (M := 3) 4,
    ← D5.S3.Quantum.Algebra.WeylPhaseArithmetic.windowRoot_pow_mod (M := 3) 5,
    ← D5.S3.Quantum.Algebra.WeylPhaseArithmetic.windowRoot_pow_mod (M := 3) 6,
    ← D5.S3.Quantum.Algebra.WeylPhaseArithmetic.windowRoot_pow_mod (M := 3) 8,
    ← D5.S3.Quantum.Algebra.WeylPhaseArithmetic.windowRoot_pow_mod (M := 3) 10,
    ← D5.S3.Quantum.Algebra.WeylPhaseArithmetic.windowRoot_pow_mod (M := 3) 12]
  all_goals norm_num [h20, h21, Ne.symm h20, Ne.symm h21, hn1, hn2, ZMod, Fin.ext_iff, Fin.neg_def, map_ofNat]
  all_goals try simp +decide only [↓reduceIte, Ne.symm h20, Ne.symm h21]
  all_goals linear_combination (-1 / 24 : ℂ) * root_sum

private theorem law_nonneg (p : ZMod 3 × ZMod 3) :
    (law p).im = 0 ∧ 0 ≤ (law p).re := by
  by_cases h : p = (0, 0) <;> norm_num [law, h]

private theorem law_sum : ∑ p, law p = 1 := by
  norm_num [Fintype.sum_prod_type, sum_three, law,
    show (2 : ZMod 3) ≠ 0 by decide]

private theorem law_support : coordinateSupport law = 8 := by
  classical
  have h : (Finset.univ.filter fun p => law p ≠ 0) =
      (Finset.univ : Finset (ZMod 3 × ZMod 3)).erase (0, 0) := by
    ext p
    simp [law]
  rw [coordinateSupport, h]
  norm_num

private theorem law_entropy : coordinateEntropy law = Real.log 8 := by
  classical
  let J := {p : ZMod 3 × ZMod 3 // p ≠ (0, 0)}
  let f : J → ℝ := fun p => (law p.1).re
  have hcard : Fintype.card J = 8 := by
    simp [J, Fintype.card_subtype_compl]
  have hsum : ∑ p : J, law p.1 = 1 := by
    have h := Fintype.sum_eq_add_sum_subtype_ne law (0, 0)
    rw [law_sum] at h
    simpa [law, J] using h.symm
  have hp : (∀ p, 0 ≤ f p) ∧ ∑ p, f p = 1 := by
    refine ⟨fun p => (law_nonneg p.1).2, ?_⟩
    have h := congrArg Complex.re hsum
    simpa [f] using h
  have : Nonempty J := ⟨⟨(0, 1), by decide⟩⟩
  have hu : f = fun _ => (Fintype.card J : ℝ)⁻¹ := by
    funext p
    norm_num [f, law, p.2, hcard]
  have he := (D5.S3.Entropy.EntropyEquality.entropy_eq_log_card_iff_uniform f hp).mpr hu
  have hz := Fintype.sum_eq_add_sum_subtype_ne (fun p => Real.negMulLog (law p).re) (0, 0)
  calc
    coordinateEntropy law = shannonEntropy f := by
      simpa [coordinateEntropy, shannonEntropy, f, law, J] using hz
    _ = Real.log 8 := by simpa [hcard] using he

/-- The only-dimension-multiples assertion fails in the source's own qutrit frame. -/
theorem result : ¬ claim := by
  intro h
  have ht : (Matrix.trace (rho * rho)).re = (3 / 8 : ℝ) := by
    rw [rho_purity]
    norm_num
  have he : coordinateEntropy law = -Real.log (3 / 8 : ℝ) + Real.log 3 := by
    rw [law_entropy, Real.log_div (by norm_num) (by norm_num)]
    ring
  have hh := h (ZMod 3) (ZMod 3 × ZMod 3) (by norm_num)
    (fun p => grossLocal 3 p.1 p.2) qutrit_frame_allowed rho rho_density.1 rho_density.2
  simp only [qutrit_coordinates, ht] at hh
  have hsat := hh law_nonneg (by norm_num) (by norm_num) (by simpa using he)
  obtain ⟨delta, hd1, hd3, hd⟩ := hsat
  rw [law_support] at hd
  norm_num at hd3 hd
  omega

end D5.S3.Quantum.Magic.ThioSaturationRefutation
