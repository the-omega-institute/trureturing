/- GID: D5/S3/FiniteGroups/RegularRepresentation/RegularTrace
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/RegularRepresentation/RegularTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Regular trace of ordered weighted group-algebra products, including the empty product. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. The complete license and immutable source are
in Library/FiniteGroups/tauceti2026finitecharacters.md.
Authors: The Tau Ceti contributors

The diagonal trace argument is adapted from
TauCeti.trace_leftMulMatrix_monoidAlgebra at the revision cited there.
Use the equivalent declaration directly when the repository's pinned Mathlib
supplies it, and remove the corresponding port.
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Trace

/-! # The regular trace identity for finite group algebras -/

@[expose] public section

namespace D5.S3.FiniteGroups.RegularRepresentation.RegularTrace

open scoped BigOperators

set_option autoImplicit false

/-- The trace of an ordered product of left-multiplication operators is the group
order times the identity coefficient of the product. Arbitrary coefficients and
the empty list of factors are included over every commutative ring. -/
theorem trace_lmul_list_prod {R H : Type*} [CommRing R] [Group H] [Fintype H]
    (a : List (MonoidAlgebra R H)) :
    LinearMap.trace R (MonoidAlgebra R H)
        ((a.map (Algebra.lmul R (MonoidAlgebra R H))).prod) =
      (Fintype.card H : R) * a.prod.coeff 1 := by
  classical
  rw [← map_list_prod, LinearMap.trace_eq_matrix_trace R (MonoidAlgebra.basis H R)]
  have hdiag : ∀ g : H,
      (a.prod * MonoidAlgebra.single g (1 : R)).coeff g = a.prod.coeff 1 := fun g => by
    simpa using a.prod.coeff_mul_single_eq_coeff_mul (m₁ := g) (r := 1) 1 (by simp)
  simp only [Matrix.trace, Matrix.diag_apply, Algebra.toMatrix_lmul']
  change (∑ g : H, (a.prod * MonoidAlgebra.single g 1).coeff g) = _
  simp [hdiag]

end D5.S3.FiniteGroups.RegularRepresentation.RegularTrace
