/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueRows
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueRows
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant]
   utility: none
   digest: Seven simultaneous value and derivative comparisons determine the evaluated critical rows along the residue line. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate

open MvPolynomial Polynomial

private theorem lift_value_samples (ab : Fin 4 × Fin 4)
    (h : ∀ t : Fin 7, slicedObservation imaginary (point ((t : ℕ) : F)) ab =
      valueAt ((t : ℕ) : F) ab) :
    ∀ u : F, slicedObservation imaginary (point u) ab = valueAt u ab := by
  let p := affineRestriction (V imaginary ab)
  let q := ofFn 7 (valueCoefficients ab.1 ab.2)
  have hp : p.natDegree ≤ 6 :=
    (natDegree_affineRestriction_le _).trans (observation_totalDegree_slice _ _)
  have hpq : p = q := by
    apply eq_of_natDegree_lt_card_of_eval_eq _ _ (distinct_points (by decide : 7 ≤ 1009))
    · intro t
      rw [show p = affineRestriction (V imaginary ab) from rfl, eval_affineRestriction,
        eval_value, show q = ofFn 7 _ from rfl, eval_ofFn]
      exact h t
    · simpa only [Fintype.card_fin] using
        max_lt (Nat.lt_succ_of_le hp) (ofFn_natDegree_lt (by decide) _)
  intro u
  have hh := congrArg (Polynomial.eval u : F[X] → F) hpq
  simpa only [p, q, eval_affineRestriction, eval_value, eval_ofFn, valueAt] using hh

private theorem lift_partial_samples (r : Fin 10) (j : Fin 5)
    (h : ∀ t : Fin 7, partialValue imaginary (point ((t : ℕ) : F)) (observedRow r) j =
      partialAt ((t : ℕ) : F) r j) :
    ∀ u : F, partialValue imaginary (point u) (observedRow r) j = partialAt u r j := by
  let p := affineRestriction (pderiv j (V imaginary (observedRow r)))
  let q := ofFn 7 (partialCoefficients r j)
  have hp : p.natDegree ≤ 5 :=
    (natDegree_affineRestriction_le _).trans (partial_totalDegree_slice _ _ _)
  have hpq : p = q := by
    apply eq_of_natDegree_lt_card_of_eval_eq _ _ (distinct_points (by decide : 7 ≤ 1009))
    · intro t
      rw [show p = affineRestriction (pderiv j (V imaginary (observedRow r))) from rfl,
        eval_affineRestriction, eval_partial, show q = ofFn 7 _ from rfl, eval_ofFn]
      exact h t
    · simpa only [Fintype.card_fin] using
        max_lt (show p.natDegree < 7 by omega) (ofFn_natDegree_lt (by decide) _)
  intro u
  have hh := congrArg (Polynomial.eval u : F[X] → F) hpq
  simpa only [p, q, eval_affineRestriction, eval_partial, eval_ofFn, partialAt] using hh

theorem evaluatedRows_eq (u : F) (deleted : Fin 10)
    (hv : ∀ (t : Fin 7) ab, slicedObservation imaginary (point ((t : ℕ) : F)) ab =
      valueAt ((t : ℕ) : F) ab)
    (hp : ∀ (t : Fin 7) r j, partialValue imaginary (point ((t : ℕ) : F)) (observedRow r) j =
      partialAt ((t : ℕ) : F) r j) :
    (criticalMatrix imaginary deleted).map (MvPolynomial.eval (point u)) = evaluatedRows u deleted := by
  ext i j
  simp only [Matrix.map_apply, criticalMatrix, evaluatedRows]
  split
  · rw [eval_partial]
    exact lift_partial_samples _ _ (fun t => hp t _ _) u
  · split
    · rw [eval_value]
      exact lift_value_samples _ (fun t => hv t _) u
    · rw [map_rotationObservation]
      simp only [MvPolynomial.eval_C, MvPolynomial.eval_X, rotationObservation]
      rw [lift_value_samples _ (fun t => hv t _) u, lift_value_samples _ (fun t => hv t _) u]

end D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate
