/- GID: D5/S3/PrimeForms/Symmetry/InversionAntisymmetricSum
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Symmetry/InversionAntisymmetricSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An integer-valued inversion-antisymmetric function sums to zero on a finite group. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Algebra.Ring.Int.Defs

namespace D5.S3.PrimeForms.Symmetry.InversionAntisymmetricSum

/-- An integer-valued function on a finite group that changes sign under inversion has total sum
zero. Inversion pairs distinct elements, while antisymmetry and characteristic zero force the value
at every self-inverse element to vanish. -/
theorem inversion_antisymmetric_sum_eq_zero {G : Type*} [Group G] [Fintype G]
    (f : G → ℤ) (hanti : ∀ g, f g⁻¹ = -f g) : ∑ g, f g = 0 := by
  classical
  simpa using Finset.sum_ninvolution (s := Finset.univ) (f := f) Inv.inv
    (fun g => by rw [hanti g, add_neg_cancel])
    (fun g hne hfix => by
      have hfixedValue : f g = -f g := (congrArg f hfix).symm.trans (hanti g)
      exact hne ((CharZero.eq_neg_self_iff (R := ℤ)).mp hfixedValue))
    (fun _ => Finset.mem_univ _)
    (fun g => inv_inv g)

end D5.S3.PrimeForms.Symmetry.InversionAntisymmetricSum
