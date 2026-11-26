/- GID: D5/S3/Quantum/Divergence/CompleteHockeyStick/NonlinearCurve
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/CompleteHockeyStick/NonlinearCurve
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: The complete hockey-stick curve has quadratic loss near zero under full Kraus span and the Choi support criterion. -/

import D5.S3.Quantum.Divergence.CompleteHockeyStick.NonlinearUpper
import D5.S3.Quantum.Divergence.CompleteHockeyStickChoiSupport

/-! Quadratic loss near zero for the complete hockey-stick curve. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Divergence.CompleteHockeyStickNonlinearCurve

open _root_.Matrix
open scoped CStarAlgebra ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState QuantumChannel)
open D5.S3.Quantum.Foundation.FiniteDensityPurification (toMState)
open D5.S3.Quantum.Divergence.CanonicalChannelDPI (actual_kraus_representation)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (E amp ptr)
open D5.S3.Quantum.Divergence.CompleteHockeyStickNonlinearUpper (exists_uniform_nonlinear_upper)
open D5.S3.Quantum.Divergence.CompleteHockeyStickChoiSupport (exists_budget_witness)
open UnitaryReconstruction.LiuWildChoiObstruction (normalizedChoi pairMatrix)

open private E_contract from D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

private def completeCurveValues (N : QuantumChannel A B) (γ a : ℝ) : Set ℝ :=
  {y | ∃ (R : Type) (fR : Fintype R) (dR : DecidableEq R),
    letI := fR
    letI := dR
    ∃ ρ σ : Matrix (R × A) (R × A) ℂ,
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ σ.PosSemidef ∧ σ.trace = 1 ∧
      ptr ρ = ptr σ ∧ E γ ρ σ ≤ a ∧ y = E γ (amp N ρ) (amp N σ)}

/-- The supremum of output hockey-stick divergence over finite reference systems and
equal-reference-marginal density pairs of input divergence at most `a`, with zero included. -/
def completeCurve (N : QuantumChannel A B) (γ a : ℝ) : ℝ :=
  sSup (insert 0 (completeCurveValues N γ a))

private theorem exists_density_with_matrix {n : Type} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (hX : X.PosSemidef) (htr : X.trace = 1) :
    ∃ ρ : DensityState n, (toMState ρ).m = X := by
  let ρ : DensityState n :=
    ⟨CStarMatrix.ofMatrix X, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hX.nonneg, htr⟩
  exact ⟨ρ, rfl⟩

private theorem nonlinear_bound_mono {K d x a : ℝ} (hK : 1 ≤ K) (hd : 0 < d)
    (hx : 0 ≤ x) (hxa : x ≤ a) :
    x - x ^ 2 / (K ^ 2 * (2 * x + d)) ≤ a - a ^ 2 / (K ^ 2 * (2 * a + d)) := by
  have hKsq : 1 ≤ K ^ 2 := by nlinarith only [hK, sq_nonneg (K - 1)]
  have hKpos : 0 < K ^ 2 := zero_lt_one.trans_le hKsq
  have hxDen : 0 < 2 * x + d := by linarith only [hx, hd]
  have haDen : 0 < 2 * a + d := by linarith only [hx, hxa, hd]
  have hquot : (2 * a * x + d * (a + x)) / ((2 * a + d) * (2 * x + d)) ≤ 1 / 2 := by
    apply (div_le_iff₀ (mul_pos haDen hxDen)).mpr
    nlinarith only [sq_nonneg d]
  have hdiff : a ^ 2 / (2 * a + d) - x ^ 2 / (2 * x + d) =
      (a - x) * ((2 * a * x + d * (a + x)) / ((2 * a + d) * (2 * x + d))) := by
    rw [← mul_div_assoc, eq_div_iff (mul_ne_zero haDen.ne' hxDen.ne')]
    calc
      _ = a ^ 2 * (2 * x + d) - x ^ 2 * (2 * a + d) := by
        rw [sub_mul, ← mul_assoc (a ^ 2 / (2 * a + d)), div_mul_cancel₀ _ haDen.ne',
          mul_comm (2 * a + d) (2 * x + d), ← mul_assoc (x ^ 2 / (2 * x + d)),
          div_mul_cancel₀ _ hxDen.ne']
      _ = _ := by ring
  have hscaled : (a ^ 2 / (2 * a + d) - x ^ 2 / (2 * x + d)) / K ^ 2 ≤ a - x := by
    apply (div_le_iff₀ hKpos).mpr
    calc
      _ ≤ (a - x) * (1 / 2) := by
        rw [hdiff]
        exact mul_le_mul_of_nonneg_left hquot (sub_nonneg.mpr hxa)
      _ ≤ a - x := mul_le_of_le_one_right (sub_nonneg.mpr hxa) (by norm_num)
      _ ≤ (a - x) * K ^ 2 := le_mul_of_one_le_right (sub_nonneg.mpr hxa) hKsq
  simp only [sub_div, div_div, mul_comm (2 * a + d) (K ^ 2),
    mul_comm (2 * x + d) (K ^ 2)] at hscaled
  linarith only [hscaled]

/-- The loss of the complete nonlinear curve has quadratic order at zero for a full
Kraus-product span and a normalized Choi support containing no full reference factor over
a nonzero output vector. This addresses the nonlinear direction in arXiv:2608.27171v1, §9, fourth bullet. -/
theorem quadratic_loss_near_zero [Nonempty A] (N : QuantumChannel A B) (γ : ℝ) (hγ : 1 < γ)
    (hspan : Submodule.span ℂ
      (Set.range fun p : (Fin (Fintype.card B) × Fin (Fintype.card A)) ×
          (Fin (Fintype.card B) × Fin (Fintype.card A)) =>
        ((actual_kraus_representation N).kraus p.1)ᴴ *
          (actual_kraus_representation N).kraus p.2) = ⊤)
    (hS : ∀ v : B → ℂ, (∀ i : A, (fun p : A × B => if p.1 = i then v p.2 else 0) ∈
      (pairMatrix (normalizedChoi N)).mulVecLin.range) → v = 0) :
    ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ ∀ a : ℝ, 0 < a → a ≤ δ →
      c * a ^ 2 ≤ a - completeCurve N γ a ∧ a - completeCurve N γ a ≤ C * a ^ 2 := by
  classical
  obtain ⟨K, hK, hUniform⟩ := exists_uniform_nonlinear_upper.{0, 0, 0} N hspan
  obtain ⟨R, fR, dR, δ, D, hδ, hD, hWitness⟩ := exists_budget_witness N γ hγ hS
  let g (x : ℝ) : ℝ := x - x ^ 2 / (K ^ 2 * (2 * x + (γ - 1)))
  have hg0 : g 0 = 0 := by simp [g]
  have hmono {x a : ℝ} (hx : 0 ≤ x) (hxa : x ≤ a) : g x ≤ g a :=
    nonlinear_bound_mono hK (sub_pos.mpr hγ) hx hxa
  have hKsq : 0 < K ^ 2 := pow_pos (zero_lt_one.trans_le hK) _
  have hdenδ : 0 < K ^ 2 * (2 * δ + (γ - 1)) := mul_pos hKsq (by linarith only [hδ, hγ])
  refine ⟨(K ^ 2 * (2 * δ + (γ - 1)))⁻¹, D + 1, δ, inv_pos.mpr hdenδ,
    by linarith only [hD], hδ, ?_⟩
  intro a ha haδ
  have hg : 0 ≤ g a := by simpa only [hg0] using hmono (x := 0) le_rfl ha.le
  have hUpper : g a ∈ upperBounds (insert 0 (completeCurveValues N γ a)) := by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact hg
    rcases hy with ⟨S, fS, dS, ρ, σ, hρ, htρ, hσ, htσ, hm, hinput, rfl⟩
    let := fS
    let := dS
    by_cases hx : 0 < E γ ρ σ
    · obtain ⟨ρ', hρ'⟩ := exists_density_with_matrix ρ hρ htρ
      obtain ⟨σ', hσ'⟩ := exists_density_with_matrix σ hσ htσ
      have hm' : ptr (toMState ρ').m = ptr (toMState σ').m := by
        simpa only [hρ', hσ'] using hm
      have hx' : 0 < E γ (toMState ρ').m (toMState σ').m := by
        simpa only [hρ', hσ'] using hx
      have hy : E γ (amp N ρ) (amp N σ) ≤ g (E γ ρ σ) := by
        simpa only [hρ', hσ', g, add_sub_assoc] using
          (@hUniform S fS dS γ hγ.le ρ' σ' hm' hx')
      exact hy.trans (hmono hx.le hinput)
    · exact (E_contract N γ hρ hσ).trans ((le_of_not_gt hx).trans hg)
  have hCurveUpper : completeCurve N γ a ≤ g a :=
    csSup_le ⟨0, Set.mem_insert _ _⟩ (fun _ hy => hUpper hy)
  let := fR
  let := dR
  obtain ⟨ρ, σ, hρ, htρ, hσ, htσ, hm, _hpositive, hinput, hpay⟩ := hWitness a ha haδ
  have hmem : E γ (amp N ρ) (amp N σ) ∈ completeCurveValues N γ a :=
    ⟨R, fR, dR, ρ, σ, hρ, htρ, hσ, htσ, hm, hinput, rfl⟩
  have hCurveLower : a / (1 + D * a) ≤ completeCurve N γ a :=
    hpay.trans (le_csSup ⟨g a, hUpper⟩ (Set.mem_insert_of_mem _ hmem))
  constructor
  · have hdena : 0 < K ^ 2 * (2 * a + (γ - 1)) := mul_pos hKsq (by linarith only [ha, hγ])
    calc
      _ = a ^ 2 / (K ^ 2 * (2 * δ + (γ - 1))) := by rw [div_eq_mul_inv, mul_comm]
      _ ≤ a ^ 2 / (K ^ 2 * (2 * a + (γ - 1))) :=
        div_le_div_of_nonneg_left (sq_nonneg a) hdena
          (mul_le_mul_of_nonneg_left (by linarith only [haδ]) hKsq.le)
      _ = a - g a := by simp only [g, sub_sub_cancel]
      _ ≤ a - completeCurve N γ a := sub_le_sub_left hCurveUpper a
  · have hden : 1 ≤ 1 + D * a := le_add_of_nonneg_right (mul_nonneg hD ha.le)
    have hden0 : 0 < 1 + D * a := zero_lt_one.trans_le hden
    calc
      _ ≤ a - a / (1 + D * a) := sub_le_sub_left hCurveLower a
      _ = D * a ^ 2 / (1 + D * a) := by
        field_simp [hden0.ne']
        ring
      _ ≤ D * a ^ 2 := div_le_self (mul_nonneg hD (sq_nonneg a)) hden
      _ ≤ (D + 1) * a ^ 2 :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (sq_nonneg a)

end D5.S3.Quantum.Divergence.CompleteHockeyStickNonlinearCurve
