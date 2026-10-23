/- GID: D5/S3/Quantum/Matrix/TwoPointFunctionalCalculus
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/TwoPointFunctionalCalculus
   mirror-E: none(waiver:consumed-helper-extraction)
   anchors: []
   utility: none
   digest: Shared existing two-point functional calculus on self-adjoint matrix involutions. -/

import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder

namespace QuantumTwoPointFunctionalCalculus

/- The proofs below are extracted, without mathematical duplication, from the
existing cumulant-Renyi refutation. That module and the generic Hiai TILDE
classification both consume them. No independent mathematical gain is claimed. -/

theorem involution_spectrum {n : Type} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : IsSelfAdjoint H) (hHH : H * H = 1)
    {x : ℝ} (hx : x ∈ spectrum ℝ H) : x = 1 ∨ x = -1 := by
  have hc : cfc (fun x : ℝ => x * x) H = cfc (fun _ : ℝ => 1) H := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) H, cfc_id' ℝ H hH,
      cfc_const 1 H hH, Algebra.algebraMap_eq_smul_one]
    simpa using hHH
  have hsq := eqOn_of_cfc_eq_cfc hc (ha := hH) (by fun_prop) (by fun_prop) hx
  dsimp at hsq
  rcases eq_or_eq_neg_of_sq_eq_sq x 1 (by nlinarith) with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem two_point_cfc {n : Type} [Fintype n] [DecidableEq n]
    (f : ℝ → ℝ) (a b : ℝ) (H : Matrix n n ℂ)
    (hH : IsSelfAdjoint H) (hHH : H * H = 1) :
    cfc f (a • (1 : Matrix n n ℂ) + b • H) =
      ((f (a+b) + f (a-b))/2) • (1 : Matrix n n ℂ) +
      ((f (a+b) - f (a-b))/2) • H := by
  have haff : cfc (fun x : ℝ => a + b*x) H = a • (1 : Matrix n n ℂ) + b • H := by
    rw [cfc_const_add a (fun x : ℝ => b*x) H (by fun_prop) hH,
      cfc_const_mul_id b H hH, Algebra.algebraMap_eq_smul_one]
  rw [← haff, ← cfc_comp f (fun x : ℝ => a+b*x) H hH
    ((H.finite_real_spectrum.image _).continuousOn _) (by fun_prop)]
  calc
    cfc (fun x : ℝ => f (a+b*x)) H =
      cfc (fun x : ℝ => (f (a+b)+f (a-b))/2 + ((f (a+b)-f (a-b))/2)*x) H := by
      apply cfc_congr
      intro x hx
      rcases involution_spectrum H hH hHH hx with rfl | rfl <;> dsimp <;>
        simp only [mul_one, mul_neg_one, ← sub_eq_add_neg] <;> ring
    _ = _ := by
      rw [cfc_const_add _ (fun x : ℝ => ((f (a+b)-f (a-b))/2)*x) H (by fun_prop) hH,
        cfc_const_mul_id _ H hH, Algebra.algebraMap_eq_smul_one]


#print axioms two_point_cfc

end QuantumTwoPointFunctionalCalculus
