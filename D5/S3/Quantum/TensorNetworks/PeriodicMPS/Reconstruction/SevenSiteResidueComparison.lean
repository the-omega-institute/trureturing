/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueComparison
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueComparison
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueRows, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueBezout]
   utility: none
   digest: Forty-seven node evaluations identify the affine restriction of an exact literal cofactor quotient. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueRows
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueNodes
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueBezout

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate

open Polynomial

def node (t : Fin 47) : F := ((nodes t : ℕ) : F)

private theorem nodes_injective : Function.Injective node := by
  apply (distinct_points (le_refl 1009)).comp
  intro x y h
  have hval := congrArg Fin.val h
  simp only [nodes] at hval
  apply Fin.ext
  split at hval <;> split at hval <;> omega

private theorem node_k_ne_zero (t : Fin 47) : point (node t) 1 ≠ 0 := by
  fin_cases t <;> decide +kernel

/-- The affine restriction of any exact quotient is identified by its samples.
The degree bound for the quotient follows from the bound for the actual cofactor. -/
theorem identify_line_quotient (deleted : Fin 10) (hd : deleted = 0 ∨ deleted = 1)
    (p : Slice F) (hp : (criticalMatrix imaginary deleted).det = MvPolynomial.X 1 * p)
    (hv : ∀ (t : Fin 7) ab, slicedObservation imaginary (point ((t : ℕ) : F)) ab =
      valueAt ((t : ℕ) : F) ab)
    (hj : ∀ (t : Fin 7) r j, partialValue imaginary (point ((t : ℕ) : F)) (observedRow r) j =
      partialAt ((t : ℕ) : F) r j)
    (hs : ∀ t : Fin 47, (evaluatedRows (node t) deleted).det =
      point (node t) 1 * quotientValue deleted (node t)) :
    affineRestriction p = lineQuotient deleted := by
  obtain ⟨q, hq, hdegree⟩ := critical_cofactor_quotient imaginary imaginary_sq
    (by decide : (6 : F) ≠ 0) deleted
  have hpq : p = q := mul_left_cancel₀ (MvPolynomial.X_ne_zero _) (hp.symm.trans hq)
  subst q
  apply eq_of_natDegree_lt_card_of_eval_eq _ _ nodes_injective
  · intro t
    apply mul_left_cancel₀ (node_k_ne_zero t)
    rw [eval_lineQuotient, eval_affineRestriction, ← hs]
    rw [← evaluatedRows_eq (node t) deleted hv hj]
    change _ = (((MvPolynomial.eval (point (node t))).mapMatrix
      (criticalMatrix imaginary deleted))).det
    rw [← RingHom.map_det, hp, map_mul, MvPolynomial.eval_X]
  · have hbound := (natDegree_affineRestriction_le p).trans hdegree
    rw [lineQuotient_degree deleted hd, Fintype.card_fin]
    exact Nat.lt_succ_of_le (max_le hbound le_rfl)

end D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate
