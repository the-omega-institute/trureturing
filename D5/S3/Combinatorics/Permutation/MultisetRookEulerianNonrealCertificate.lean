/- GID: D5/S3/Combinatorics/Permutation/MultisetRookEulerianNonrealCertificate
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/MultisetRookEulerianNonrealCertificate
   mirror-E: none(waiver:exact-finite-certificate)
   anchors: []
   utility: none
   digest: An exact translated Newton inequality obstructs splitting of the degree-nine factor. -/

import D5.S3.Analytic.RealRootedCoefficientNewton
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.Permutation.MultisetRookEulerianNonrealCertificate

open Polynomial

noncomputable def Q : ℝ[X] :=
  monomial 0 1 + monomial 1 261 + monomial 2 21704 + monomial 3 591814 +
  monomial 4 5372605 + monomial 5 18550680 + monomial 6 27147806 +
  monomial 7 17137014 + monomial 8 4318325 + monomial 9 352440

-- Explicit translated polynomial. The identity below checks these rational
-- coefficients in Lean; Python output is not trusted by this proof.
noncomputable def P : ℝ[X] :=
  C (147002524734936505239773 / 12500000000000000000000000) +
  C (-23217846032368454006421 / 25000000000000000000000) * X +
  C (12818006465516640352661 / 1562500000000000000) * X^2 +
  C (2581464854892924348421 / 6250000000000000) * X^3 +
  C (28564835712704361409 / 6250000000000) * X^4 +
  C (213920906710892673 / 12500000000) * X^5 +
  C (20373395700847 / 781250) * X^6 +
  C (105169514469 / 6250) * X^7 +
  C (107244434 / 25) * X^8 + 352440 * X^9

theorem translate_eq : Q.comp (X + C (-9 / 1000)) = P := by
  change taylor (-9 / 1000) Q = P
  have hq : Q.natDegree ≤ 9 := by unfold Q; compute_degree!
  have hp : P.natDegree ≤ 9 := by unfold P; compute_degree!
  apply (ext_iff_natDegree_le (by simpa using hq) hp).2
  intro k hk
  rw [taylor_coeff]
  interval_cases k <;>
    norm_num [Q, P, map_add, hasseDeriv_monomial, hasseDeriv_apply_one,
      eval_monomial, Nat.choose]

theorem translated_not_splits : ¬ P.Splits := by
  intro hs
  have hd : P.natDegree = 9 := by unfold P; compute_degree!
  have hl : P.leadingCoeff = 352440 := by
    rw [← coeff_natDegree, hd]
    norm_num [P]
  have hcard : P.roots.card = 9 := hs.natDegree_eq_card_roots.symm.trans hd
  have h0 := coeff_eq_esymm_roots_of_splits hs (k := 0) (by omega)
  have h1 := coeff_eq_esymm_roots_of_splits hs (k := 1) (by omega)
  have h2 := coeff_eq_esymm_roots_of_splits hs (k := 2) (by omega)
  rw [hd, hl] at h0 h1 h2
  norm_num at h0 h1 h2
  have e9 : P.roots.esymm 9 = -P.coeff 0 / 352440 := by linarith [h0]
  have e8 : P.roots.esymm 8 = P.coeff 1 / 352440 := by linarith [h1]
  have e7 : P.roots.esymm 7 = -P.coeff 2 / 352440 := by linarith [h2]
  have hn := D5.S3.Analytic.RealRootedCoefficientNewton.esymm_mul_esymm_le_sq_esymm P.roots 7
  rw [hcard] at hn
  norm_num at hn
  rw [e7, e8, e9] at hn
  norm_num [P] at hn

theorem factor_not_splits : ¬ Q.Splits := by
  intro hs
  exact translated_not_splits (translate_eq ▸ hs.comp_X_add_C (-9 / 1000))

/-- The exact full polynomial does not split over the real field. -/
theorem full_explicit_not_splits : ¬ (X^2 * Q).Splits := by
  simpa only [pow_two, mul_assoc, splits_X_mul] using factor_not_splits

#print axioms translate_eq
#print axioms translated_not_splits
#print axioms factor_not_splits
#print axioms full_explicit_not_splits

end D5.S3.Combinatorics.Permutation.MultisetRookEulerianNonrealCertificate
