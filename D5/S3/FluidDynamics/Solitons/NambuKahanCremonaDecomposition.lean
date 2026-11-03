/- GID: D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Graffeo--Gubbiotti's generic quadratic Nambu KHK map factors through cremona -/

import D5.S3.Observer.Hankel.PositiveGramianBalancing
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! Graffeo--Gubbiotti's generic quadratic Nambu KHK map factors through the
standard four-dimensional Cremona lift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.FluidDynamics.Solitons.NambuKahanCremonaDecomposition

open Matrix
open scoped Matrix

noncomputable section

private def complexMatrix (A : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  A.map (algebraMap ℝ ℂ)

private def nambuLinearPart (A B : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j =>
    crossProduct (complexMatrix A *ᵥ x)
        (complexMatrix B *ᵥ (Pi.single j 1)) i +
      crossProduct (complexMatrix A *ᵥ (Pi.single j 1))
        (complexMatrix B *ᵥ x) i

/-- The source KHK matrix, with its linear part written by cross-product columns. -/
def kahanMatrix (A B : Matrix (Fin 3) (Fin 3) ℝ) (h : ℝ) (X : Fin 4 → ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  (X 3) • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
    (2 * (h : ℂ)) • nambuLinearPart A B (fun i : Fin 3 => X i.castSucc)

/-- The homogeneous KHK lift of the quadratic Nambu system. -/
def kahan (A B : Matrix (Fin 3) (Fin 3) ℝ) (h : ℝ) (X : Fin 4 → ℂ) : Fin 4 → ℂ :=
  Fin.snoc ((kahanMatrix A B h X).adjugate *ᵥ (fun i : Fin 3 => X i.castSucc))
    (kahanMatrix A B h X).det

/-- The standard cubic Cremona lift in four homogeneous coordinates. -/
def cremona (X : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![X 1 * X 2 * X 3, X 0 * X 2 * X 3, X 0 * X 1 * X 3, X 0 * X 1 * X 2]

def claim : Prop :=
  ∀ A B : Matrix (Fin 3) (Fin 3) ℝ, A.PosDef → B.PosDef →
    (∀ t : ℝ, 2 ≤ (B - t • A).rank) →
      ∀ h : ℝ, 0 < h →
        ∃ l₁ l₂ : Matrix (Fin 4) (Fin 4) ℂ,
          IsUnit l₁.det ∧ IsUnit l₂.det ∧
            ∀ X : Fin 4 → ℂ, kahan A B h X = l₂ *ᵥ cremona (l₁ *ᵥ X)

private def eulerJacobian (a₁ a₂ a₃ : ℂ) (y : Fin 3 → ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, a₁ * y 2, a₁ * y 1;
     a₂ * y 2, 0, a₂ * y 0;
     a₃ * y 1, a₃ * y 0, 0]

private def eulerMatrix (a₁ a₂ a₃ h : ℂ) (X : Fin 4 → ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  (X 3) • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
    (h / 2) • eulerJacobian a₁ a₂ a₃ (fun i : Fin 3 => X i.castSucc)

private def eulerPhi (a₁ a₂ a₃ h : ℂ) (X : Fin 4 → ℂ) : Fin 4 → ℂ :=
  Fin.snoc ((eulerMatrix a₁ a₂ a₃ h X).adjugate *ᵥ (fun i : Fin 3 => X i.castSucc))
    (eulerMatrix a₁ a₂ a₃ h X).det

private def g₀ : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, -1, -1, -1;
     -1, 1, -1, -1;
     -1, -1, 1, -1;
     -1, -1, -1, 1]

private def T (h : ℂ) (α β γ : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![-β * γ * h, -α * γ * h, α * β * h, -2;
      β * γ * h, -α * γ * h, -α * β * h, -2;
      -β * γ * h, α * γ * h, -α * β * h, -2;
      β * γ * h, α * γ * h, α * β * h, -2]

private theorem euler_top_identity (a₁ a₂ a₃ h α β γ : ℂ)
    (hα : α ^ 2 = a₁) (hβ : β ^ 2 = a₂) (hγ : γ ^ 2 = a₃) :
    ∀ X : Fin 4 → ℂ,
      T h α β γ *ᵥ eulerPhi a₁ a₂ a₃ h X =
        (-1 / 8 : ℂ) • (g₀ *ᵥ cremona (T h α β γ *ᵥ X)) := by
  intro X
  rw [← hα, ← hβ, ← hγ]
  funext i
  fin_cases i <;>
    simp [T, eulerPhi, eulerMatrix, eulerJacobian, g₀,
      cremona, Matrix.adjugate_fin_three, Matrix.det_fin_three,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

private theorem det_T (h α β γ : ℂ) :
    (T h α β γ).det = 32 * α ^ 2 * β ^ 2 * γ ^ 2 * h ^ 3 := by
  simp [T, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove]
  ring

private theorem g₀_unit : IsUnit g₀.det := by
  have hdet : g₀.det = -16 := by
    simp [g₀, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
      Matrix.submatrix, Fin.succAbove]
    ring
  rw [hdet]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

private theorem whitening
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (hrank : ∀ t : ℝ, 2 ≤ (B - t • A).rank) :
    ∃ P : Matrix (Fin 3) (Fin 3) ℝ, IsUnit P.det ∧
      ∃ mu : Fin 3 → ℝ,
        Pᵀ * A * P = 1 ∧ Pᵀ * B * P = diagonal mu ∧
          ∀ i j : Fin 3, i ≠ j → mu i ≠ mu j := by
  classical
  let L := D5.S3.Observer.Hankel.PositiveGramianBalancing.gramianRoot A
  obtain ⟨hLp, hLs, hLL⟩ :=
    D5.S3.Observer.Hankel.PositiveGramianBalancing.gramianRoot_spec A hA
  change L.PosDef at hLp
  change Lᴴ = L at hLs
  change L * L = A at hLL
  have hLd : IsUnit L.det := (Matrix.isUnit_iff_isUnit_det L).mp hLp.isUnit
  have hLt : Lᵀ = L := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hLs
  let S := L⁻¹
  have hSd : IsUnit S.det := Matrix.isUnit_nonsing_inv_det L hLd
  have hSt : Sᵀ = S := by simp only [S, Matrix.transpose_nonsing_inv, hLt]
  have hSA : Sᵀ * A * S = 1 := by
    rw [hSt, ← hLL]
    simp only [S, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hLd,
      Matrix.one_mul, Matrix.mul_nonsing_inv _ hLd]
  let K := Sᵀ * B * S
  have hK : K.IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_mul S hB.isHermitian
  let Q := hK.eigenvectorUnitary
  let mu := hK.eigenvalues
  have hQtQ : (Q : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * Q = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self Q
  have hQK : (Q : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * K * Q = diagonal mu := by
    simpa only [Q, mu, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def,
      RCLike.ofReal_real_eq_id, id_eq]
      using hK.conjStarAlgAut_star_eigenvectorUnitary
  let P := S * (Q : Matrix (Fin 3) (Fin 3) ℝ)
  have hPd : IsUnit P.det := by
    rw [show P = S * (Q : Matrix (Fin 3) (Fin 3) ℝ) from rfl, Matrix.det_mul]
    exact hSd.mul ((Matrix.isUnit_iff_isUnit_det _).mp Unitary.isUnit_coe)
  have hPA : Pᵀ * A * P = 1 := by
    calc
      _ = (Q : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * (Sᵀ * A * S) * Q := by
        simp only [P, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hSA, Matrix.mul_one, hQtQ]
  have hPB : Pᵀ * B * P = diagonal mu := by
    simpa only [P, K, Matrix.transpose_mul, Matrix.mul_assoc] using hQK
  refine ⟨P, hPd, mu, hPA, hPB, ?_⟩
  have hr (t : ℝ) : 2 ≤ (diagonal (fun i => mu i - t)).rank := by
    have he : Pᵀ * (B - t • A) * P = diagonal (fun i => mu i - t) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        hPA, hPB, Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]
    rw [← he, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hPd,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by simpa using hPd)]
    exact hrank t
  intro i j hij he
  have hn := hr (mu i)
  rw [Matrix.rank_diagonal, Fintype.card_subtype] at hn
  have hs : ({k : Fin 3 | mu k - mu i ≠ 0} : Finset (Fin 3)) ⊆ Finset.univ \ {i, j} := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_ne_zero] at hk
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, true_and, not_or]
    constructor
    · intro hki
      subst k
      exact hk rfl
    · intro hkj
      subst k
      exact hk he.symm
  have hc := Finset.card_le_card hs
  have hcard : (Finset.univ \ ({i, j} : Finset (Fin 3))).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [hij]
  omega

private def liftP (P : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j =>
    if hi : i.val < 3 then
      if hj : j.val < 3 then
        complexMatrix P ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else 0
    else if j.val < 3 then 0 else 1

private theorem liftP_unit (P : Matrix (Fin 3) (Fin 3) ℝ) (hP : IsUnit P.det) :
    IsUnit (liftP P).det := by
  have hd : (liftP P).det = (P.det : ℂ) := by
    simp [liftP, complexMatrix, Matrix.det_succ_row_zero,
      Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove]
  rw [hd]
  exact hP.map (algebraMap ℝ ℂ)

private theorem liftP_action (P : Matrix (Fin 3) (Fin 3) ℝ) (X : Fin 4 → ℂ) :
    liftP P *ᵥ X =
      Fin.snoc (complexMatrix P *ᵥ (fun i : Fin 3 => X i.castSucc)) (X 3) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]
    simp [liftP, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · rw [Fin.snoc_castSucc]
    fin_cases j <;>
      simp [liftP, complexMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private def eulerCoefficients (P : Matrix (Fin 3) (Fin 3) ℝ) (mu : Fin 3 → ℝ) :
    Fin 3 → ℂ :=
  ![4 / (P.det : ℂ) * ((mu 2 : ℂ) - mu 1),
    4 / (P.det : ℂ) * ((mu 0 : ℂ) - mu 2),
    4 / (P.det : ℂ) * ((mu 1 : ℂ) - mu 0)]

private theorem cross_matrix_adjugate (Q : Matrix (Fin 3) (Fin 3) ℂ)
    (u v : Fin 3 → ℂ) :
    crossProduct (Q *ᵥ u) (Q *ᵥ v) = Q.adjugateᵀ *ᵥ crossProduct u v := by
  funext i
  fin_cases i <;>
    simp [cross_apply, Matrix.adjugate_fin_three, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

private theorem adjugate_scaled_inverse (Q : Matrix (Fin 3) (Fin 3) ℂ)
    (hQ : IsUnit Q.det) : Q.adjugate = Q.det • Q⁻¹ := by
  apply Matrix.ext_of_mulVec_single
  intro i
  simpa only [Matrix.cramer_eq_adjugate_mulVec, Matrix.smul_mulVec] using
    (Matrix.det_smul_inv_mulVec_eq_cramer Q (Pi.single i 1) hQ).symm

private theorem adjugate_conjugate (Q M : Matrix (Fin 3) (Fin 3) ℂ)
    (hQ : IsUnit Q.det) :
    (Q * M * Q⁻¹).adjugate = Q * M.adjugate * Q⁻¹ := by
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
    adjugate_scaled_inverse Q hQ,
    adjugate_scaled_inverse Q⁻¹ (Matrix.isUnit_nonsing_inv_det Q hQ),
    Matrix.nonsing_inv_nonsing_inv _ hQ, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    mul_inv_cancel₀ (isUnit_iff_ne_zero.mp hQ), one_smul, Matrix.mul_assoc]

private theorem cross_inverse_transpose (Q : Matrix (Fin 3) (Fin 3) ℂ)
    (hQ : IsUnit Q.det) (u v : Fin 3 → ℂ) :
    crossProduct (Qᵀ⁻¹ *ᵥ u) (Qᵀ⁻¹ *ᵥ v) =
      Q.det⁻¹ • (Q *ᵥ crossProduct u v) := by
  rw [cross_matrix_adjugate, adjugate_scaled_inverse Qᵀ⁻¹
    (Matrix.isUnit_nonsing_inv_det Qᵀ (by simpa using hQ)), Matrix.transpose_smul,
    Matrix.nonsing_inv_nonsing_inv _ (by simpa using hQ), Matrix.transpose_transpose,
    Matrix.det_nonsing_inv, Matrix.det_transpose, Ring.inverse_eq_inv, Matrix.smul_mulVec]

private theorem nambu_action (A B : Matrix (Fin 3) (Fin 3) ℝ)
    (x v : Fin 3 → ℂ) :
    nambuLinearPart A B x *ᵥ v =
      crossProduct (complexMatrix A *ᵥ x) (complexMatrix B *ᵥ v) +
        crossProduct (complexMatrix A *ᵥ v) (complexMatrix B *ᵥ x) := by
  funext i
  fin_cases i <;>
    simp [nambuLinearPart, cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

private theorem covariance
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (h : ℝ)
    (P : Matrix (Fin 3) (Fin 3) ℝ) (mu : Fin 3 → ℝ)
    (hP : IsUnit P.det)
    (hA : Pᵀ * A * P = 1) (hB : Pᵀ * B * P = diagonal mu) :
    ∀ Z : Fin 4 → ℂ,
      kahan A B h (liftP P *ᵥ Z) =
        liftP P *ᵥ eulerPhi (eulerCoefficients P mu 0)
          (eulerCoefficients P mu 1) (eulerCoefficients P mu 2) (h : ℂ) Z := by
  intro Z
  let Q := complexMatrix P
  let D : Matrix (Fin 3) (Fin 3) ℂ := diagonal (fun i => (mu i : ℂ))
  let a := eulerCoefficients P mu
  have hdQ : Q.det = (P.det : ℂ) := (RingHom.map_det (algebraMap ℝ ℂ) P).symm
  have hQ : IsUnit Q.det := by
    rw [hdQ]
    exact hP.map (algebraMap ℝ ℂ)
  have hQt : IsUnit Qᵀ.det := by simpa only [Matrix.det_transpose] using hQ
  have hcA : Qᵀ * complexMatrix A * Q = 1 := by
    change Pᵀ.map (algebraMap ℝ ℂ) * A.map (algebraMap ℝ ℂ) *
      P.map (algebraMap ℝ ℂ) = 1
    rw [← Matrix.map_mul, ← Matrix.map_mul, hA]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hcB : Qᵀ * complexMatrix B * Q = D := by
    change Pᵀ.map (algebraMap ℝ ℂ) * B.map (algebraMap ℝ ℂ) *
      P.map (algebraMap ℝ ℂ) = diagonal (fun i => (mu i : ℂ))
    rw [← Matrix.map_mul, ← Matrix.map_mul, hB,
      Matrix.diagonal_map (map_zero (algebraMap ℝ ℂ))]
    rfl
  have hAP : complexMatrix A * Q = Qᵀ⁻¹ := by
    calc
      _ = Qᵀ⁻¹ * (Qᵀ * complexMatrix A * Q) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQt,
          Matrix.one_mul]
      _ = _ := by rw [hcA, Matrix.mul_one]
  have hBP : complexMatrix B * Q = Qᵀ⁻¹ * D := by
    calc
      _ = Qᵀ⁻¹ * (Qᵀ * complexMatrix B * Q) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQt,
          Matrix.one_mul]
      _ = _ := by rw [hcB]
  have hJ (y v : Fin 3 → ℂ) :
      Q.det⁻¹ • (crossProduct y (D *ᵥ v) + crossProduct v (D *ᵥ y)) =
        (1 / 4 : ℂ) • (eulerJacobian (a 0) (a 1) (a 2) y *ᵥ v) := by
    rw [hdQ]
    funext i
    fin_cases i <;>
      simp [D, a, eulerCoefficients, eulerJacobian, cross_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring
  have hL (y v : Fin 3 → ℂ) :
      nambuLinearPart A B (Q *ᵥ y) *ᵥ (Q *ᵥ v) =
        (1 / 4 : ℂ) • (Q *ᵥ (eulerJacobian (a 0) (a 1) (a 2) y *ᵥ v)) := by
    rw [nambu_action]
    simp only [Matrix.mulVec_mulVec, hAP, hBP]
    rw [← Matrix.mulVec_mulVec y Qᵀ⁻¹ D, ← Matrix.mulVec_mulVec v Qᵀ⁻¹ D,
      cross_inverse_transpose Q hQ, cross_inverse_transpose Q hQ,
      ← smul_add, ← Matrix.mulVec_add, ← Matrix.mulVec_smul, hJ, Matrix.mulVec_smul]
    simp only [Matrix.mulVec_mulVec]
  have hLM (y : Fin 3 → ℂ) :
      nambuLinearPart A B (Q *ᵥ y) * Q =
        (1 / 4 : ℂ) • (Q * eulerJacobian (a 0) (a 1) (a 2) y) := by
    apply Matrix.ext_of_mulVec_single
    intro j
    simpa only [Matrix.mulVec_mulVec, Matrix.smul_mulVec] using hL y (Pi.single j 1)
  let M := eulerMatrix (a 0) (a 1) (a 2) (h : ℂ) Z
  have hX : (fun i : Fin 3 => (liftP P *ᵥ Z) i.castSucc) =
      Q *ᵥ (fun i : Fin 3 => Z i.castSucc) := by
    rw [liftP_action]
    simp only [Fin.snoc_castSucc]
    rfl
  have hW : (liftP P *ᵥ Z) 3 = Z 3 := by rw [liftP_action]; rfl
  have hMQ : kahanMatrix A B h (liftP P *ᵥ Z) * Q = Q * M := by
    dsimp only [kahanMatrix]
    rw [hX, hW, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.one_mul, hLM, smul_smul]
    dsimp only [M, eulerMatrix]
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul]
    congr 2
    ring
  have hM : kahanMatrix A B h (liftP P *ᵥ Z) = Q * M * Q⁻¹ := by
    calc
      _ = (kahanMatrix A B h (liftP P *ᵥ Z) * Q) * Q⁻¹ :=
        (Matrix.mul_nonsing_inv_cancel_right Q _ hQ).symm
      _ = _ := by rw [hMQ]
  rw [kahan, hM, adjugate_conjugate Q M hQ,
    Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det _).mpr hQ), hX,
    liftP_action]
  dsimp only [eulerPhi]
  simp only [Fin.snoc_castSucc]
  congr 1
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ,
    Matrix.mul_one]
  exact (Matrix.mulVec_mulVec _ Q M.adjugate).symm

private theorem assembly
    (he : ∀ (a₁ a₂ a₃ h α β γ : ℂ), α ^ 2 = a₁ → β ^ 2 = a₂ → γ ^ 2 = a₃ →
      ∀ X : Fin 4 → ℂ,
        T h α β γ *ᵥ eulerPhi a₁ a₂ a₃ h X =
          (-1 / 8 : ℂ) • (g₀ *ᵥ cremona (T h α β γ *ᵥ X)))
    (hd : ∀ (h α β γ : ℂ),
      (T h α β γ).det = 32 * α ^ 2 * β ^ 2 * γ ^ 2 * h ^ 3)
    (hg : IsUnit g₀.det)
    (hw : ∀ (A B : Matrix (Fin 3) (Fin 3) ℝ), A.PosDef → B.PosDef →
      (∀ t : ℝ, 2 ≤ (B - t • A).rank) →
      ∃ P : Matrix (Fin 3) (Fin 3) ℝ, IsUnit P.det ∧
        ∃ mu : Fin 3 → ℝ,
          Pᵀ * A * P = 1 ∧ Pᵀ * B * P = diagonal mu ∧
            ∀ i j : Fin 3, i ≠ j → mu i ≠ mu j)
    (hc : ∀ (A B : Matrix (Fin 3) (Fin 3) ℝ) (h : ℝ)
      (P : Matrix (Fin 3) (Fin 3) ℝ) (mu : Fin 3 → ℝ), IsUnit P.det →
      Pᵀ * A * P = 1 → Pᵀ * B * P = diagonal mu →
      ∀ Z : Fin 4 → ℂ,
        kahan A B h (liftP P *ᵥ Z) =
          liftP P *ᵥ eulerPhi (eulerCoefficients P mu 0)
            (eulerCoefficients P mu 1) (eulerCoefficients P mu 2) (h : ℂ) Z) :
    claim := by
  intro A B hA hB hrank h hh
  obtain ⟨P, hP, mu, hPA, hPB, hmu⟩ := hw A B hA hB hrank
  let a := eulerCoefficients P mu
  have hpn : (P.det : ℂ) ≠ 0 := by
    exact_mod_cast isUnit_iff_ne_zero.mp hP
  have han : ∀ i : Fin 3, a i ≠ 0 := by
    intro i
    fin_cases i <;> dsimp [a, eulerCoefficients] <;>
      apply mul_ne_zero (div_ne_zero (by norm_num) hpn) <;>
      apply sub_ne_zero.mpr
    · exact_mod_cast hmu 2 1 (by decide)
    · exact_mod_cast hmu 0 2 (by decide)
    · exact_mod_cast hmu 1 0 (by decide)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (a 0) (by decide : 0 < 2)
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (a 1) (by decide : 0 < 2)
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq (a 2) (by decide : 0 < 2)
  let R := liftP P
  let V := T (h : ℂ) α β γ
  have hR : IsUnit R.det := liftP_unit P hP
  have hV : IsUnit V.det := by
    rw [show V = T (h : ℂ) α β γ from rfl, hd, hα, hβ, hγ]
    apply isUnit_iff_ne_zero.mpr
    have hhn : (h : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hh
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (han 0)) (han 1)) (han 2)) (pow_ne_zero 3 hhn)
  let U := V * R⁻¹
  have hU : IsUnit U.det := by
    rw [show U = V * R⁻¹ from rfl, Matrix.det_mul]
    exact hV.mul (Matrix.isUnit_nonsing_inv_det R hR)
  refine ⟨U, (-1 / 8 : ℂ) • (U⁻¹ * g₀), hU, ?_, ?_⟩
  · rw [Matrix.det_smul, Matrix.det_mul]
    exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num : (-1 / 8 : ℂ) ≠ 0))).mul
      ((Matrix.isUnit_nonsing_inv_det U hU).mul hg)
  · intro X
    have hRX : R *ᵥ (R⁻¹ *ᵥ X) = X := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hR, Matrix.one_mulVec]
    have hcov := hc A B h P mu hP hPA hPB (R⁻¹ *ᵥ X)
    change kahan A B h (R *ᵥ (R⁻¹ *ᵥ X)) =
      R *ᵥ eulerPhi (a 0) (a 1) (a 2) (h : ℂ) (R⁻¹ *ᵥ X) at hcov
    rw [hRX] at hcov
    have hE := he (a 0) (a 1) (a 2) (h : ℂ) α β γ hα hβ hγ (R⁻¹ *ᵥ X)
    change V *ᵥ eulerPhi (a 0) (a 1) (a 2) (h : ℂ) (R⁻¹ *ᵥ X) =
      (-1 / 8 : ℂ) • (g₀ *ᵥ cremona (V *ᵥ (R⁻¹ *ᵥ X))) at hE
    have hUK : U *ᵥ kahan A B h X =
        (-1 / 8 : ℂ) • (g₀ *ᵥ cremona (U *ᵥ X)) := by
      rw [hcov]
      simpa only [U, Matrix.mulVec_mulVec, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hR, Matrix.mul_one] using hE
    calc
      kahan A B h X = U⁻¹ *ᵥ (U *ᵥ kahan A B h X) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
      _ = _ := by
        rw [hUK, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_mulVec]


theorem result : claim := by
  apply assembly
  · intro a₁ a₂ a₃ h α β γ hα hβ hγ
    exact euler_top_identity a₁ a₂ a₃ h α β γ hα hβ hγ
  · intro h α β γ
    exact det_T h α β γ
  · exact g₀_unit
  · intro A B hA hB hrank
    exact whitening A B hA hB hrank
  · intro A B h P mu hP hA hB
    exact covariance A B h P mu hP hA hB

run_cmd do
  let root := `D5.S3.FluidDynamics.Solitons.NambuKahanCremonaDecomposition.result
  let claimName := `D5.S3.FluidDynamics.Solitons.NambuKahanCremonaDecomposition.claim
  let auditEnv ← Lean.importModules
    #[{ module := `D5.S3.FluidDynamics.Solitons.NambuKahanCremonaDecomposition }] {}
  let auditEnv := auditEnv.setExporting false
  let some owner := auditEnv.getModuleIdxFor? root | throwError "missing module index"
  let mut owned : Array Lean.Name := #[]
  for (name, _) in auditEnv.constants.toList do
    if auditEnv.getModuleIdxFor? name == some owner then
      owned := owned.push name
  owned := owned.qsort Lean.Name.quickLt
  let mut pending := #[root, claimName]
  let mut seen : Lean.NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    if let some info := auditEnv.find? name then
      pending := pending ++ info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants
  let unused := owned.filter (fun name => !seen.contains name)
  let axioms := seen.toList.filter fun name =>
    if let some (.axiomInfo _) := auditEnv.find? name then true else false
  let json := Lean.Json.mkObj [
    ("module", Lean.toJson auditEnv.allImportedModuleNames[owner.toNat]!.toString),
    ("owned", Lean.toJson (owned.map Lean.Name.toString)),
    ("unused", Lean.toJson (unused.map Lean.Name.toString)),
    ("axioms", Lean.toJson (axioms.map Lean.Name.toString)),
    ("closure_size", Lean.toJson seen.size)]
  IO.FS.writeFile "scratch-lane-math-op-nambu-kahan-cremona/closure-audit.json" json.pretty
  logInfo m!"CLOSURE_AUDIT owned={owned.size} unused={unused} axioms={axioms}"

#print axioms result

end

end D5.S3.FluidDynamics.Solitons.NambuKahanCremonaDecomposition
