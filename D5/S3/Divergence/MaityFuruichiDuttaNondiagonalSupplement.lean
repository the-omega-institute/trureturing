/- GID: D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement
   generality: I
   mirror-B: D5/B/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement
   mirror-E: none(waiver:source-supplement)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.claim; result=D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.result; claim=D5/S3/Divergence/MaityFuruichiDuttaNondiagonalSupplement.claim
   digest: The existing Tsallis ordering reversal in a common nondiagonal basis. -/

/- Source: Haobo Ma and Wenlin Zhang, 3 November 2026 supplement answering
   Supriyo Dutta. CC BY 4.0. This is a change-of-basis supplement to the
   existing refutation, not another conjecture resolution.
   All old matrix functions and old pair computations are consumed directly. -/
import D5.S3.Divergence.MaityFuruichiDuttaOrderingRefutation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder

namespace D5.S3.Divergence.MaityFuruichiDuttaNondiagonalSupplement
open MaityFuruichiDuttaOrderingRefutation

private lemma map_cfc_unitary {n : ℕ} (u : unitary (Matrix (Fin n) (Fin n) ℂ))
    (f : ℝ → ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    let e := Unitary.conjStarAlgAut ℂ _ u
    e (cfc f X) = cfc f (e X) := by
  dsimp only
  let e := Unitary.conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ) u
  by_cases hX : IsSelfAdjoint X
  · exact StarAlgHomClass.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint)
      e f X (X.finite_real_spectrum.continuousOn _)
      e.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional hX (hX.map e)
  · have hE : ¬ IsSelfAdjoint (e X) := fun h => hX (h.of_map e e.injective)
    rw [cfc_apply_of_not_predicate X hX, cfc_apply_of_not_predicate (e X) hE]
    exact map_zero e

/-- Simultaneous unitary conjugation preserves the actual three source functions. -/
theorem functions_unitary {n : ℕ} (u : unitary (Matrix (Fin n) (Fin n) ℂ))
    (ρ σ : Matrix (Fin n) (Fin n) ℂ) (α r z q : ℝ) :
    let e := Unitary.conjStarAlgAut ℂ _ u
    renyiRZ α r z (e ρ) (e σ) = renyiRZ α r z ρ σ ∧
    B2 α q (e ρ) (e σ) = B2 α q ρ σ ∧
    tsallis α (e ρ) (e σ) = tsallis α ρ σ := by
  let e := Unitary.conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ) u
  have ht (X : Matrix (Fin n) (Fin n) ℂ) : trace (e X) = trace X := by
    change trace ((u : Matrix (Fin n) (Fin n) ℂ) * X * star (u : Matrix (Fin n) (Fin n) ℂ)) = _
    rw [trace_mul_cycle, u.prop.1, one_mul]
  have hc (f : ℝ → ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
      e (cfc f X) = cfc f (e X) := map_cfc_unitary u f X
  change renyiRZ α r z (e ρ) (e σ) = _ ∧ B2 α q (e ρ) (e σ) = _ ∧
    tsallis α (e ρ) (e σ) = _
  constructor
  · simp only [renyiRZ, ← hc, ← map_mul, ht]
  constructor
  · simp only [B2, ← hc, ← map_mul, ht]
  · simp only [tsallis, ← hc, ← map_mul, ← map_sub, ht]

/-- The common real orthogonal change of basis, viewed over the complex numbers. -/
def U : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / Real.sqrt 2 : ℝ) • !![1, 1; 1, -1]

/-- Both states are expressed in the same basis. -/
def rhohat : Matrix (Fin 2) (Fin 2) ℂ := !![1/2, 3/10; 3/10, 1/2]
def sigmahat : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((125 + 12 * Real.sqrt 6) / 250 : ℝ), -69/250;
      -69/250, ((125 - 12 * Real.sqrt 6) / 250 : ℝ)]

private lemma U_star : star U = U := by
  change U.conjTranspose = U
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [U, Matrix.conjTranspose_apply, Complex.real_smul]

private lemma U_square : U * U = 1 := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (show (0:ℝ)<2 by norm_num)))
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [U, Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul, Matrix.one_apply] <;>
    push_cast <;> field_simp <;> ring_nf <;> norm_num [hs]

private def u : unitary (Matrix (Fin 2) (Fin 2) ℂ) :=
  ⟨U, by exact ⟨by rw [U_star, U_square], by rw [U_star, U_square]⟩⟩

private lemma common_basis : rhohat = U * rho * star U ∧ sigmahat = U * sigma * star U := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (show (0:ℝ)<2 by norm_num)))
  rw [U_star]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [U, rhohat, sigmahat, rho, sigma, Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul] <;>
    push_cast <;> field_simp <;> ring_nf <;> norm_num [hs] <;> ring

private lemma pair_values :
    renyiRZ (1/2) (1/2) 2 rho sigma =
      4 * (1 - Real.sqrt ((2117 + 288 * Real.sqrt 2) / 3125)) ∧
    B2 (1/2) 1 rho sigma = 2 - 20 / Real.sqrt 154 := by
  constructor
  · unfold renyiRZ lnr
    norm_num only
    rw [sandwich_trace, ← Real.sqrt_eq_rpow]
    ring
  · unfold B2
    norm_num only [Real.rpow_one]
    rw [cfc_id' (p := IsSelfAdjoint) ℝ sigma (show IsSelfAdjoint sigma from pair_states.2.2.1.1), sandwich_A,
      cfc_id' (p := IsSelfAdjoint) ℝ A A_nonneg.isSelfAdjoint]
    have hl : cfc (fun x:ℝ => lnr (1/2) x) A =
        (2:ℝ) • (cfc (fun x:ℝ => x^(1/2:ℝ)) A - 1) := by
      have he : (fun x:ℝ => lnr (1/2) x) = (fun x:ℝ => 2 * (x^(1/2:ℝ) - 1)) := by
        funext x; unfold lnr; ring
      rw [he, cfc_const_mul (2:ℝ) (fun x:ℝ => x^(1/2:ℝ) - 1) A
        (A.finite_real_spectrum.continuousOn _),
        cfc_sub (fun x:ℝ => x^(1/2:ℝ)) (fun _ : ℝ => 1) A
          (A.finite_real_spectrum.continuousOn _) (by fun_prop),
        cfc_const 1 A A_nonneg.isSelfAdjoint]
      simp [Algebra.algebraMap_eq_smul_one]
    rw [hl, A_sqrt]
    norm_num [rho, A, Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.one_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      Fin.sum_univ_two, Complex.real_smul]
    ring

private lemma pair_tsallis : tsallis (1/2) rho sigma = 48/125 := by
  have hlow : (1/5:ℝ)^(1/2:ℝ) = 1 / Real.sqrt 5 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num)]; norm_num
  have hhigh : (4/5:ℝ)^(1/2:ℝ) = 2 / Real.sqrt 5 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num)]; norm_num
  unfold tsallis
  norm_num only
  rw [(pair_cfc _).1, (pair_cfc _).2, hhigh, hlow]
  have hs : (Real.sqrt 5 : ℂ)^2 = 5 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have hn : (Real.sqrt 5 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (show (0:ℝ)<5 by norm_num)))
  norm_num [rho, H, K, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Complex.real_smul]
  push_cast
  field_simp
  ring_nf
  have h4 : Real.sqrt 5 ^ 4 = 25 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ)≤5 by norm_num), sq_nonneg (Real.sqrt 5 ^ 2 - 5)]
  norm_num [h4]

/-- Positive definite density states, their exact entries, and the nonzero commutator. -/
theorem matrix_facts :
    rhohat.PosDef ∧ rhohat.trace = 1 ∧ sigmahat.PosDef ∧ sigmahat.trace = 1 ∧
    rhohat.det = 4/25 ∧ sigmahat.det = 4/25 ∧
    rhohat 0 1 = 3/10 ∧ rhohat 1 0 = 3/10 ∧
    sigmahat 0 1 = -69/250 ∧ sigmahat 1 0 = -69/250 ∧
    (rhohat * sigmahat - sigmahat * rhohat) 0 1 = (-18 * Real.sqrt 6 / 625 : ℝ) ∧
    rhohat * sigmahat ≠ sigmahat * rhohat := by
  have hrp : rhohat.PosDef := by
    rw [common_basis.1]
    exact (Unitary.isUnit_coe (U := u)).posDef_star_right_conjugate_iff.mpr pair_states.1
  have hsp : sigmahat.PosDef := by
    rw [common_basis.2]
    exact (Unitary.isUnit_coe (U := u)).posDef_star_right_conjugate_iff.mpr pair_states.2.2.1
  have hs : (Real.sqrt 6 : ℂ)^2 = 6 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  have hc : (rhohat * sigmahat - sigmahat * rhohat) 0 1 = (-18 * Real.sqrt 6 / 625 : ℝ) := by
    norm_num [rhohat, sigmahat, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast; ring
  refine ⟨hrp, ?_, hsp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hc, ?_⟩
  · norm_num [rhohat, Matrix.trace, Fin.sum_univ_two]
  · norm_num [sigmahat, Matrix.trace, Fin.sum_univ_two]; push_cast; ring
  · norm_num [rhohat, Matrix.det_fin_two]
  · norm_num [sigmahat, Matrix.det_fin_two]
    push_cast; ring_nf; norm_num [hs]
  · norm_num [rhohat]
  · norm_num [rhohat]
  · norm_num [sigmahat]
  · norm_num [sigmahat]
  · intro he
    have hz : (rhohat * sigmahat - sigmahat * rhohat) 0 1 = 0 := by rw [he, sub_self]; rfl
    rw [hc] at hz
    have hp := Real.sqrt_pos.mpr (show (0:ℝ)<6 by norm_num)
    have hz' := congrArg Complex.re hz
    norm_num at hz'

/-- Each state has the two eigenvalues 4/5 and 1/5, each with multiplicity one. -/
theorem characteristic_polynomials :
    rhohat.charpoly = (Polynomial.X - Polynomial.C (4/5:ℂ)) * (Polynomial.X - Polynomial.C (1/5:ℂ)) ∧
    sigmahat.charpoly = (Polynomial.X - Polynomial.C (4/5:ℂ)) * (Polynomial.X - Polynomial.C (1/5:ℂ)) := by
  obtain ⟨_, hr, _, hs, hd, he, _⟩ := matrix_facts
  constructor <;> rw [Matrix.charpoly_fin_two]
  · rw [hr, hd]
    apply Polynomial.funext
    intro x
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    ring
  · rw [hs, he]
    apply Polynomial.funext
    intro x
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    ring

/-- A common orthogonal conjugation, with covariance for every real spectral function. -/
theorem common_orthogonal_conjugation :
    star U = U ∧ U * U = 1 ∧
    rhohat = U * rho * star U ∧ sigmahat = U * sigma * star U ∧
    (∀ (f : ℝ → ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ),
      cfc f (U * X * star U) = U * cfc f X * star U) ∧
    rhohat * sigmahat - sigmahat * rhohat = U * (rho * sigma - sigma * rho) * star U := by
  refine ⟨U_star, U_square, common_basis.1, common_basis.2, ?_, ?_⟩
  · intro f X
    exact (map_cfc_unitary u f X).symm
  · rw [common_basis.1, common_basis.2]
    have hU : star U * U = 1 := by rw [U_star, U_square]
    calc
      _ = U * rho * (star U * U) * sigma * star U - U * sigma * (star U * U) * rho * star U := by noncomm_ring
      _ = _ := by rw [hU]; noncomm_ring

/-- The source parameter conditions hold at alpha = r = 1/2, z = 2, q = 1. -/
theorem parameter_conditions :
    (0:ℝ) ≤ 1/2 ∧ (1/2:ℝ) < 1 ∧ (1/2:ℝ) ≠ 0 ∧ (0:ℝ) < 2 ∧ (1-(1/2:ℝ)) < 1 := by
  norm_num

/-- The inner fidelity trace and inverse-power sandwich are transported by the same U. -/
theorem spectral_quantities :
    (trace (cfc (fun x:ℝ => x^(2:ℝ))
      (cfc (fun x:ℝ => x^(1/8:ℝ)) sigmahat *
        cfc (fun x:ℝ => x^(1/4:ℝ)) rhohat *
        cfc (fun x:ℝ => x^(1/8:ℝ)) sigmahat))).re =
      (2117 + 288 * Real.sqrt 2) / 3125 ∧
    cfc (fun x:ℝ => x^(-(1/2:ℝ))) rhohat * sigmahat *
      cfc (fun x:ℝ => x^(-(1/2:ℝ))) rhohat = U * A * star U := by
  let e := Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) u
  have hc (f : ℝ → ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
      e (cfc f X) = cfc f (e X) := map_cfc_unitary u f X
  have ht (X : Matrix (Fin 2) (Fin 2) ℂ) : trace (e X) = trace X := by
    change trace (U * X * star U) = trace X
    rw [trace_mul_cycle, U_star, U_square, one_mul]
  have hr : rhohat = e rho := common_basis.1
  have hs : sigmahat = e sigma := common_basis.2
  constructor
  · rw [hr, hs]
    simp only [← hc, ← map_mul, ht]
    exact sandwich_trace
  · rw [hr, hs]
    change _ = e A
    simp only [← hc, ← map_mul, sandwich_A]

/-- The exact three values and strict chain at the displayed nondiagonal states. -/
theorem exact_values_and_bounds :
    renyiRZ (1/2) (1/2) 2 rhohat sigmahat =
      4 * (1 - Real.sqrt ((2117 + 288 * Real.sqrt 2) / 3125)) ∧
    B2 (1/2) 1 rhohat sigmahat = 2 - 20 / Real.sqrt 154 ∧
    tsallis (1/2) rhohat sigmahat = 48/125 ∧
    B2 (1/2) 1 rhohat sigmahat < 2/5 ∧
    (2/5:ℝ) < renyiRZ (1/2) (1/2) 2 rhohat sigmahat ∧
    tsallis (1/2) rhohat sigmahat < B2 (1/2) 1 rhohat sigmahat ∧
    B2 (1/2) 1 rhohat sigmahat < renyiRZ (1/2) (1/2) 2 rhohat sigmahat := by
  have hi := functions_unitary u rho sigma (1/2) (1/2) 2 1
  change renyiRZ (1/2) (1/2) 2 (U * rho * star U) (U * sigma * star U) = _ ∧
    B2 (1/2) 1 (U * rho * star U) (U * sigma * star U) = _ ∧
    tsallis (1/2) (U * rho * star U) (U * sigma * star U) = _ at hi
  rw [← common_basis.1, ← common_basis.2] at hi
  rw [hi.1, hi.2.1, hi.2.2]
  have hD : tsallis (1/2) rho sigma < B2 (1/2) 1 rho sigma := by
    rw [pair_tsallis, pair_values.2]
    have hp : 0 < Real.sqrt 154 := Real.sqrt_pos.mpr (by norm_num)
    have hs := Real.sq_sqrt (show (0:ℝ)≤154 by norm_num)
    have hlow : (1250/101:ℝ) < Real.sqrt 154 := by nlinarith
    have hdiv : (20:ℝ) / Real.sqrt 154 < 202/125 := (div_lt_iff₀ hp).mpr (by nlinarith)
    linarith
  exact ⟨pair_values.1, pair_values.2, pair_tsallis, B2_lt, B1_gt, hD, B2_lt.trans B1_gt⟩

/-- The previously refuted ordering restricted to two states with nonzero
off-diagonal entries in the same basis, at the source parameters. -/
def claim : Prop := ∀ ρ σ : Matrix (Fin 2) (Fin 2) ℂ,
  ρ.PosDef → ρ.trace = 1 → σ.PosDef → σ.trace = 1 → ρ * σ ≠ σ * ρ →
  ρ 0 1 ≠ 0 → σ 0 1 ≠ 0 →
  renyiRZ (1/2) (1/2) 2 ρ σ ≤ B2 (1/2) 1 ρ σ

theorem result : ¬ claim := by
  intro h
  obtain ⟨hr, hrt, hs, hst, _, _, hr01, _, hs01, _, _, hnc⟩ := matrix_facts
  have hb := h rhohat sigmahat hr hrt hs hst hnc (by rw [hr01]; norm_num) (by rw [hs01]; norm_num)
  exact (not_lt_of_ge hb) exact_values_and_bounds.2.2.2.2.2.2

#print axioms functions_unitary
#print axioms matrix_facts
#print axioms characteristic_polynomials
#print axioms common_orthogonal_conjugation
#print axioms spectral_quantities
#print axioms exact_values_and_bounds
#print axioms result

end D5.S3.Divergence.MaityFuruichiDuttaNondiagonalSupplement
