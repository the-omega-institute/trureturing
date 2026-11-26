/- GID: D5/S3/Quantum/Semigroups/WuPhysicalHighHigh
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuPhysicalHighHigh
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact signed two-mode jump identities and the two-square high-high cost. -/

import D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The two-mode physical correlation identities (2.1)–(2.6) for the jumps
in Wu v1, Remark 3.15.
The occupation order is 00, 01, 10, 11. Rows are targets and the trace is
unnormalized. The matrix identities allow arbitrary complex inputs.
The high-high identities use two orthogonal unit vectors over ℂ. -/

set_option autoImplicit false

noncomputable section
open Matrix Kronecker
open scoped BigOperators Matrix
open D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison (modeJump)

namespace D5.S3.Quantum.Semigroups.WuPhysicalHighHigh

abbrev Occupation := Fin 2 × Fin 2
abbrev Mat := Matrix Occupation Occupation ℂ
abbrev Vec := Occupation → ℂ

private def J₁ : Mat := single (0, 0) (0, 1) 1 - single (1, 0) (1, 1) 1
private def J₂ : Mat := single (0, 0) (1, 0) 1 + single (0, 1) (1, 1) 1

/-- The occupation imbalance, with diagonal (1, 0, 0, −1). -/
def F : Mat :=
  diagonal fun i => if i = (0, 0) then 1 else if i = (1, 1) then -1 else 0

/-- Occupation parity, with diagonal (1, −1, −1, 1). -/
def parity : Mat := diagonal fun i => if i.1 = i.2 then 1 else -1

def omega : Mat :=
  single (0, 0) (1, 1) (-1) + single (0, 1) (1, 0) 1 -
    single (1, 0) (0, 1) 1 + single (1, 1) (0, 0) 1

def twist (X : Mat) : Mat := omega * Xᵀ * omegaᴴ
def theta (v : Vec) : Vec := omega *ᵥ star v

def phi (X : Mat) : Mat := ∑ i : Fin 2, modeJump i * X * (modeJump i)ᴴ
def psi (X : Mat) : Mat := ∑ i : Fin 2, (modeJump i)ᴴ * X * modeJump i

private theorem literal_modes : modeJump 0 = J₂ ∧ modeJump 1 = -J₁ := by
  constructor
  · change ((!![0,1;0,0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ 1) = J₂
    apply Matrix.ext
    rintro ⟨i, j⟩ ⟨k, l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [J₂, Matrix.kroneckerMap_apply, Matrix.single_apply, Matrix.one_apply]
  · change (diagonal (![-1,1] : Fin 2 → ℂ) ⊗ₖ
        (!![0,1;0,0] : Matrix (Fin 2) (Fin 2) ℂ)) = -J₁
    apply Matrix.ext
    rintro ⟨i, j⟩ ⟨k, l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [J₁, Matrix.kroneckerMap_apply, Matrix.single_apply, Matrix.diagonal_apply]

private theorem literal_jump_sums (X : Mat) :
    phi X = J₁ * X * J₁ᴴ + J₂ * X * J₂ᴴ ∧
    psi X = J₁ᴴ * X * J₁ + J₂ᴴ * X * J₂ := by
  obtain ⟨h0, h1⟩ := literal_modes
  constructor <;> simp [phi, psi, Fin.sum_univ_two, h0, h1, add_comm]

set_option maxHeartbeats 1000000 in
-- The two identities require simplifying all entries of the sparse sandwiches.
/-- Equations (2.1) and (2.2) for the two literal signed lowering modes. -/
private theorem superoperator_identities (X : Mat) :
    phi X + psi X =
      X.trace • (1 : Mat) - (1 / 2 : ℂ) • X - twist X -
        (1 / 2 : ℂ) • (parity * X * parity) ∧
    phi X - psi X =
      X.trace • F - (F * X).trace • (1 : Mat) - (F * twist X + twist X * F) := by
  obtain ⟨hp, hq⟩ := literal_jump_sums X
  rw [hp, hq]
  -- Reduce each sparse sandwich by Eᵢₐ X Eᵦⱼ = Xₐᵦ Eᵢⱼ.
  simp only [J₁, J₂, twist, omega, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_single, star_one, star_neg, add_mul, sub_mul, mul_add, mul_sub,
    Matrix.single_mul_mul_single]
  constructor <;> apply Matrix.ext <;> rintro ⟨i, j⟩ ⟨k, l⟩ <;>
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [F, parity, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply,
      Matrix.transpose_apply, Matrix.trace, Matrix.diag, Matrix.one_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, smul_eq_mul] <;> ring

def pairing (u v : Vec) : ℂ := star u ⬝ᵥ v
def imbalance (u : Vec) : ℝ := (pairing u (F *ᵥ u)).re
def eta (u v : Vec) : ℂ := pairing u (parity *ᵥ v)
def sigma (u v : Vec) : ℂ := pairing u (theta v)
def tau (u v : Vec) : ℂ := pairing u (F *ᵥ theta v)

/-- The same target-row, source-column weight as in the directed crossing tables. -/
def weight (u v : Vec) : ℝ := ∑ i : Fin 2, Complex.normSq (pairing u (modeJump i *ᵥ v))

private def outer (a b : Vec) : Mat := vecMulVec a (star b)
private def quadratic (u : Vec) (X : Mat) : ℂ := pairing u (X *ᵥ u)

private theorem quadratic_add (u : Vec) (X Y : Mat) :
    quadratic u (X + Y) = quadratic u X + quadratic u Y := by
  simp only [quadratic, pairing, Matrix.add_mulVec, dotProduct_add]

private theorem pairing_adjoint (A : Mat) (u v : Vec) :
    pairing u (Aᴴ *ᵥ v) = star (pairing v (A *ᵥ u)) := by
  unfold pairing
  rw [Matrix.mulVec_conjTranspose, Matrix.star_dotProduct_star, ← Matrix.dotProduct_mulVec]

private theorem quadratic_outer (u a b : Vec) :
    quadratic u (outer a b) = pairing u a * star (pairing u b) := by
  simp only [quadratic, pairing, outer, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMulVec,
    smul_dotProduct, smul_eq_mul, Matrix.star_dotProduct b u]

private theorem sandwich_outer (A : Mat) (a b : Vec) :
    A * outer a b * Aᴴ = outer (A *ᵥ a) (A *ᵥ b) := by
  simp only [outer, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose,
    star_star]

private theorem trace_outer (a b : Vec) : (outer a b).trace = pairing b a := by
  rw [outer, Matrix.trace_vecMulVec, pairing, dotProduct_comm]

private theorem twist_outer (v : Vec) : twist (outer v v) = outer (theta v) (theta v) := by
  simpa only [twist, theta, outer, Matrix.transpose_vecMulVec, star_star] using
    sandwich_outer omega (star v) (star v)

private theorem mul_star_eq_normSq (z : ℂ) : z * star z = (Complex.normSq z : ℂ) := by
  simpa only [Complex.star_def] using Complex.mul_conj z

private theorem star_mul_eq_normSq (z : ℂ) : star z * z = (Complex.normSq z : ℂ) := by
  rw [mul_comm, mul_star_eq_normSq]

private theorem normSq_star (z : ℂ) : Complex.normSq (star z) = Complex.normSq z := by
  simpa only [Complex.star_def] using Complex.normSq_conj z

private theorem imbalance_parity_adjoint : Fᴴ = F ∧ parityᴴ = parity := by
  constructor <;> apply Matrix.ext <;> rintro ⟨i, j⟩ ⟨k, l⟩ <;>
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [F, parity, Matrix.conjTranspose_apply, Matrix.diagonal_apply]

private theorem quadratic_jump_sums (u v : Vec) :
    quadratic u (phi (outer v v)) = (weight u v : ℂ) ∧
    quadratic u (psi (outer v v)) = (weight v u : ℂ) := by
  constructor
  · simp only [phi, weight, Fin.sum_univ_two, quadratic_add, sandwich_outer, quadratic_outer,
      mul_star_eq_normSq, Complex.ofReal_add]
  · have hs (A : Mat) :
        Aᴴ * outer v v * A = outer (Aᴴ *ᵥ v) (Aᴴ *ᵥ v) := by
      simpa only [Matrix.conjTranspose_conjTranspose] using sandwich_outer Aᴴ v v
    simp only [psi, weight, Fin.sum_univ_two, quadratic_add, hs, quadratic_outer,
      mul_star_eq_normSq, Complex.ofReal_add, pairing_adjoint, normSq_star]

private theorem high_high_sum_sub (u v : Vec) (hu : pairing u u = 1)
    (hv : pairing v v = 1) (huv : pairing u v = 0) :
    weight u v + weight v u = 1 - Complex.normSq (sigma u v) - Complex.normSq (eta u v) / 2 ∧
    weight u v - weight v u =
      imbalance u - imbalance v - 2 * (tau u v * star (sigma u v)).re := by
  obtain ⟨hF, hparity⟩ := imbalance_parity_adjoint
  obtain ⟨hp, hq⟩ := quadratic_jump_sums u v
  obtain ⟨hs, hd⟩ := superoperator_identities (outer v v)
  have hpar : parity * outer v v * parity = outer (parity *ᵥ v) (parity *ᵥ v) := by
    simpa only [hparity] using sandwich_outer parity v v
  have hleft : F * outer (theta v) (theta v) = outer (F *ᵥ theta v) (theta v) := by
    simp only [outer, Matrix.mul_vecMulVec]
  have hright : outer (theta v) (theta v) * F = outer (theta v) (F *ᵥ theta v) := by
    calc
      _ = outer (theta v) (theta v) * Fᴴ := by rw [hF]
      _ = _ := by
        simp only [outer, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose, star_star]
  have htraceF : (F * outer v v).trace = pairing v (F *ᵥ v) := by
    rw [show F * outer v v = outer (F *ᵥ v) v by simp only [outer, Matrix.mul_vecMulVec],
      trace_outer]
  have hsub (X Y : Mat) : quadratic u (X - Y) = quadratic u X - quadratic u Y := by
    simp only [quadratic, pairing, Matrix.sub_mulVec, dotProduct_sub]
  have hsmul (c : ℂ) (X : Mat) : quadratic u (c • X) = c * quadratic u X := by
    simp only [quadratic, pairing, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hone : quadratic u 1 = 1 := by
    simpa only [quadratic, Matrix.one_mulVec] using hu
  have hsum := congrArg (quadratic u) hs
  have hdiff := congrArg (quadratic u) hd
  simp only [quadratic_add, hsub, hsmul, hp, hq, trace_outer, hv, hone, hpar, twist_outer,
    quadratic_outer, huv, star_zero, mul_zero, one_mul, sub_zero, mul_star_eq_normSq] at hsum
  simp only [quadratic_add, hsub, hsmul, hp, hq, htraceF, trace_outer, hv, hone, twist_outer,
    hleft, hright, quadratic_outer, one_mul, mul_one] at hdiff
  constructor
  · have h := congrArg Complex.re hsum
    have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num [Complex.ofReal_div]
    simp only [hhalf, Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, mul_zero, sub_zero] at h
    unfold sigma eta
    linarith only [h]
  · have h := congrArg Complex.re hdiff
    change _ = (quadratic u F - pairing v (F *ᵥ v) -
      (tau u v * star (sigma u v) + sigma u v * star (tau u v))).re at h
    have hcross : (sigma u v * star (tau u v)).re = (tau u v * star (sigma u v)).re := by
      simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    simp only [quadratic, Complex.ofReal_re, Complex.add_re, Complex.sub_re, hcross] at h
    unfold imbalance
    linarith only [h]

private theorem even_pair_identity (a d b e : ℂ) :
    Complex.normSq (a * e + d * b) = Complex.normSq (star a * b + star d * e) -
      (Complex.normSq a - Complex.normSq d) * (Complex.normSq b - Complex.normSq e) := by
  simp only [Complex.normSq_apply, Complex.star_def, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

private theorem imbalance_coordinates (u : Vec) :
    imbalance u = Complex.normSq (u (0, 0)) - Complex.normSq (u (1, 1)) := by
  norm_num [imbalance, pairing, F, Matrix.mulVec_diagonal, dotProduct, Fintype.sum_prod_type,
    Fin.sum_univ_two, Pi.star_apply, mul_neg, star_mul_eq_normSq, Complex.add_re,
    Complex.neg_re, Complex.ofReal_re, Complex.normSq_apply] <;> ring

private theorem tau_coordinates (u v : Vec) :
    tau u v = -star (u (0, 0) * v (1, 1) + u (1, 1) * v (0, 0)) := by
  norm_num [tau, theta, pairing, F, omega, Matrix.mulVec, dotProduct,
    Matrix.diagonal_apply, Matrix.single_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Pi.star_apply, star_add, star_mul] <;> ring

private theorem eta_coordinates (u v : Vec) (huv : pairing u v = 0) :
    eta u v = 2 * (star (u (0, 0)) * v (0, 0) + star (u (1, 1)) * v (1, 1)) := by
  have h : eta u v + pairing u v =
      2 * (star (u (0, 0)) * v (0, 0) + star (u (1, 1)) * v (1, 1)) := by
    norm_num [eta, pairing, parity, Matrix.mulVec_diagonal, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, Pi.star_apply] <;> ring
  simpa only [huv, add_zero] using h

/-- Equations (2.3)–(2.5) for orthogonal unit vectors and both physical directions. -/
private theorem high_high_identities (u v : Vec) (hu : pairing u u = 1)
    (hv : pairing v v = 1) (huv : pairing u v = 0) :
    (weight u v + weight v u =
      1 - Complex.normSq (sigma u v) - Complex.normSq (eta u v) / 2) ∧
    (weight u v - weight v u =
      imbalance u - imbalance v - 2 * (tau u v * star (sigma u v)).re) ∧
    Complex.normSq (tau u v) = Complex.normSq (eta u v) / 4 - imbalance u * imbalance v := by
  obtain ⟨hs, hd⟩ := high_high_sum_sub u v hu hv huv
  refine ⟨hs, hd, ?_⟩
  rw [tau_coordinates, eta_coordinates u v huv, imbalance_coordinates u, imbalance_coordinates v,
    Complex.normSq_neg, normSq_star, Complex.normSq_mul]
  rw [even_pair_identity]
  norm_num

private theorem complete_squares (wp wm ru rv : ℝ) (e s t : ℂ) (dp dm rho : ℝ)
    (hρ : (dp + dm) * rho = dp - dm)
    (hs : wp + wm = 1 - Complex.normSq s - Complex.normSq e / 2)
    (hd : wp - wm = ru - rv - 2 * (t * star s).re)
    (ht : Complex.normSq t = Complex.normSq e / 4 - ru * rv) :
    dp * wp + dm * wm =
      ((dp + dm) / 2) * (1 + rho * ru) * (1 - rho * rv) -
        ((dp + dm) / 2) * ((2 - rho ^ 2) / 4) * Complex.normSq e -
        ((dp + dm) / 2) * Complex.normSq (s + (rho : ℂ) * t) := by
  have hsq : Complex.normSq (s + (rho : ℂ) * t) =
      Complex.normSq s + 2 * rho * (t * star s).re + rho ^ 2 * Complex.normSq t := by
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    ring
  calc
    dp * wp + dm * wm = (dp + dm) / 2 * (wp + wm) + (dp - dm) / 2 * (wp - wm) := by ring
    _ = ((dp + dm) / 2) * (1 + rho * ru) * (1 - rho * rv) -
          ((dp + dm) / 2) * ((2 - rho ^ 2) / 4) * Complex.normSq e -
          ((dp + dm) / 2) * Complex.normSq (s + (rho : ℂ) * t) := by
      rw [hs, hd, ← hρ, hsq, ht]
      ring

/-- Equation (2.6) includes the zero-weight case via Lean's real division.
The first equality supplies the exact directed loss in signed cubic transfer.
The second gives the weighted gaps between the two entries and any chosen caps.
The entries have target/source orders `(u, v)` and `(v, u)`, respectively. -/
theorem weighted_high_high (u v : Vec) (hu : pairing u u = 1)
    (hv : pairing v v = 1) (huv : pairing u v = 0)
    (dp dm : ℝ) (hp : 0 ≤ dp) (hm : 0 ≤ dm) :
    let A := (dp + dm) / 2
    let rho := (dp - dm) / (dp + dm)
    let product := A * (1 + rho * imbalance u) * (1 - rho * imbalance v)
    let paritySquare := A * ((2 - rho ^ 2) / 4) * Complex.normSq (eta u v)
    let twistSquare := A * Complex.normSq (sigma u v + (rho : ℂ) * tau u v)
    (dp * weight u v + dm * weight v u = product - paritySquare - twistSquare) ∧
    ∀ marginalPlus marginalMinus : ℝ,
      dp * (marginalPlus - weight u v) + dm * (marginalMinus - weight v u) =
        (dp * marginalPlus + dm * marginalMinus - product) + paritySquare + twistSquare := by
  dsimp only
  have hρ : (dp + dm) * ((dp - dm) / (dp + dm)) = dp - dm := by
    by_cases hzero : dp + dm = 0
    · have hp0 : dp = 0 := by linarith only [hm, hp, hzero]
      have hm0 : dm = 0 := by linarith only [hm, hp, hzero]
      simp [hp0, hm0]
    · field_simp [hzero]
  obtain ⟨hs, hd, ht⟩ := high_high_identities u v hu hv huv
  have hphysical := complete_squares (weight u v) (weight v u) (imbalance u) (imbalance v)
    (eta u v) (sigma u v) (tau u v) dp dm _ hρ hs hd ht
  refine ⟨hphysical, ?_⟩
  intro marginalPlus marginalMinus
  linear_combination -hphysical

end D5.S3.Quantum.Semigroups.WuPhysicalHighHigh
