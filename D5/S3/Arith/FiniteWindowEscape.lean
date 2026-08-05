/- GID: D5/S3/Arith/FiniteWindowEscape
   generality: G
   mirror-B: D5/B/S3/Arith/FiniteWindowEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite prime windows escape; finite readings retain a nonzero kernel difference. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic

namespace D5.S3.Arith.FiniteWindowEscape

/-- Every finite prime window is escaped by its product plus one: the escape
number is congruent to one modulo every prime in the window, is not itself in
the window, and has only prime divisors outside the window. In particular an
outside prime direction always remains, so no finite window is closed under
this construction.

Independently, every additive reading from an infinite group into a finite
group identifies two distinct inputs. Their nonzero difference lies in the
kernel of the reading, realizing the kernel branch of the hidden-fiber claim. -/
theorem finite_window_escape_and_hidden_fiber
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    {G A : Type*} [AddGroup G] [Infinite G] [AddGroup A] [Finite A]
    (R : G →+ A) :
    let E := S.prod id + 1
    (∀ p ∈ S, Nat.ModEq p E 1) ∧
      E ∉ S ∧
      (∃ q, Nat.Prime q ∧ q ∣ E ∧ q ∉ S) ∧
      (∀ q, Nat.Prime q → q ∣ E → q ∉ S) ∧
      ∃ x y : G, x ≠ y ∧ R x = R y ∧ x - y ≠ 0 ∧ R (x - y) = 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hp_dvd_prod : p ∣ S.prod id := Finset.dvd_prod_of_mem id hp
    simpa using
      (Nat.modEq_zero_iff_dvd.mpr hp_dvd_prod).add (Nat.ModEq.refl 1)
  · intro hEscapeMem
    have hEscapePrime := hS (S.prod id + 1) hEscapeMem
    have hEscapeDvdProd : S.prod id + 1 ∣ S.prod id :=
      Finset.dvd_prod_of_mem id hEscapeMem
    have hEscapeDvdOne : S.prod id + 1 ∣ 1 :=
      (Nat.dvd_add_iff_right hEscapeDvdProd).mpr (dvd_refl (S.prod id + 1))
    exact hEscapePrime.not_dvd_one hEscapeDvdOne
  · have hprod_pos : 0 < S.prod id :=
      Finset.prod_pos fun p hp => (hS p hp).pos
    obtain ⟨q, hqPrime, hqDvd⟩ :=
      Nat.exists_prime_and_dvd (n := S.prod id + 1) (by omega)
    refine ⟨q, hqPrime, hqDvd, ?_⟩
    intro hqMem
    have hqDvdProd : q ∣ S.prod id := Finset.dvd_prod_of_mem id hqMem
    have hqDvdOne : q ∣ 1 := (Nat.dvd_add_iff_right hqDvdProd).mpr hqDvd
    exact hqPrime.not_dvd_one hqDvdOne
  · intro q hqPrime hqDvd hqMem
    have hqDvdProd : q ∣ S.prod id := Finset.dvd_prod_of_mem id hqMem
    have hqDvdOne : q ∣ 1 := (Nat.dvd_add_iff_right hqDvdProd).mpr hqDvd
    exact hqPrime.not_dvd_one hqDvdOne
  · obtain ⟨x, y, hxy, hR⟩ := Finite.exists_ne_map_eq_of_infinite R
    refine ⟨x, y, hxy, hR, sub_ne_zero.mpr hxy, ?_⟩
    rw [map_sub, hR, sub_self]

end D5.S3.Arith.FiniteWindowEscape
