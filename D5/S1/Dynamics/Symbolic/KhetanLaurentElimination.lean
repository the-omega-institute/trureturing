/- GID: D5/S1/Dynamics/Symbolic/KhetanLaurentElimination
   generality: G
   mirror-B: none(waiver:no mirrored proof)
   mirror-E: none(waiver:no external mirror)
   anchors: []
   utility: none
   digest: Clear Laurent Bezout denominators over a coefficient fraction field. -/

import D5.S1.Dynamics.Symbolic.KhetanAnnihilator
import Mathlib.Tactic.Ring

/-!
Clearing denominators precedes any configuration action. The resulting
coefficient is proved nonzero in the coefficient domain. The localized
coprimality required by `clear_laurent_bezout` is an algebraic intermediate
obligation; this module does not derive it from a line-factor restriction.
-/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.KhetanLaurentElimination

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

private theorem coefficient_map_injective :
    Function.Injective (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R K)) := by
  intro f g h
  ext j
  apply IsFractionRing.injective R K
  simpa using congrArg (fun F : AddMonoidAlgebra K ℤ => F.coeff j) h

/-- A finite Laurent filter has a nonzero common coefficient denominator.
The support is preserved while the coefficients are returned to the domain. -/
theorem clear_laurent_coefficients (f : AddMonoidAlgebra K ℤ) :
    ∃ d : R, d ≠ 0 ∧ ∃ F : AddMonoidAlgebra R ℤ,
      AddMonoidAlgebra.mapRingHom ℤ (algebraMap R K) F =
        AddMonoidAlgebra.single 0 (algebraMap R K d) * f := by
  classical
  have hfinite := f.coeff.finite_range
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors R) hfinite.toFinset
  have hex (j : ℤ) : ∃ a : R, algebraMap R K a = (d : R) • f.coeff j :=
    hd (f.coeff j) (hfinite.mem_toFinset.mpr ⟨j, rfl⟩)
  choose C hC using hex
  have hsupport : ∀ j : ℤ, C j ≠ 0 → j ∈ f.coeff.support := by
    intro j hj
    by_contra hn
    have he := hC j
    rw [Finsupp.notMem_support_iff.mp hn, smul_zero] at he
    exact hj ((IsFractionRing.injective R K) (he.trans (map_zero _).symm))
  let F : AddMonoidAlgebra R ℤ :=
    AddMonoidAlgebra.ofCoeff (Finsupp.onFinset f.coeff.support C hsupport)
  refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp d.property, F, ?_⟩
  ext j
  change algebraMap R K (C j) =
    (AddMonoidAlgebra.single 0 (algebraMap R K (d : R)) * f).coeff j
  rw [AddMonoidAlgebra.coeff_single_zero_mul]
  simpa only [Algebra.smul_def] using hC j

/-- A Bezout identity in the fraction-field Laurent ring clears to an identity
with a nonzero constant in the original coefficient domain. -/
theorem clear_laurent_bezout (P B : AddMonoidAlgebra R ℤ)
    (hcop : IsCoprime
      (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R K) P)
      (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R K) B)) :
    ∃ ρ : R, ρ ≠ 0 ∧ ∃ α β : AddMonoidAlgebra R ℤ,
      AddMonoidAlgebra.single 0 ρ = α * P + β * B := by
  obtain ⟨a, b, hab⟩ := hcop
  obtain ⟨da, hda, A, hA⟩ := clear_laurent_coefficients (R := R) a
  obtain ⟨db, hdb, C, hC⟩ := clear_laurent_coefficients (R := R) b
  refine ⟨da * db, mul_ne_zero hda hdb,
    AddMonoidAlgebra.single 0 db * A, AddMonoidAlgebra.single 0 da * C, ?_⟩
  apply coefficient_map_injective (K := K)
  simp only [map_add, map_mul, AddMonoidAlgebra.mapRingHom_single, hA, hC]
  calc
    AddMonoidAlgebra.single 0 (algebraMap R K da * algebraMap R K db) =
        (AddMonoidAlgebra.single 0 (algebraMap R K da) *
          AddMonoidAlgebra.single 0 (algebraMap R K db)) * (a *
          AddMonoidAlgebra.mapRingHom ℤ (algebraMap R K) P + b *
          AddMonoidAlgebra.mapRingHom ℤ (algebraMap R K) B) := by
      rw [hab, mul_one, AddMonoidAlgebra.single_mul_single, zero_add]
    _ = _ := by ring

end D5.S1.Dynamics.Symbolic.KhetanLaurentElimination
