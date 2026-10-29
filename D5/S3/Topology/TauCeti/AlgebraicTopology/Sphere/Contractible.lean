import D5.S3.Topology.TauCeti.AlgebraicTopology.Singular.Sphere
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
This file is a source port adapted from TauCetiProject/TauCeti at immutable
revision `5a01f5fe3621126cccf9ba22e700493cbc7b7156`, source path
`TauCeti/AlgebraicTopology/Sphere/Contractible.lean`. Changes: import paths are namespaced under
`D5.S3.Topology.TauCeti` for this repository's pinned Mathlib. The original
Tau Ceti copyright and Apache-2.0 terms are retained in
`docs/reports/licenses/tauceti-sphere-port-LICENSE.txt`. Retire this port only
when this repository's own pinned Mathlib provides an equivalent declaration
at the full telescope and all live consumers compile with direct replacement.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Spheres are not contractible

The unit sphere of a nontrivial finite-dimensional real normed space is not contractible.
This distinguishes spherical links from ball links, including the two-point zero-sphere.
No inner product on the normed space is required: the reduced homology computation is
transported from a Euclidean space of the same dimension.

The sphere has nonzero reduced singular homology with integer coefficients in its
dimension, whereas a contractible space has zero reduced homology in every degree. See Hatcher,
*Algebraic Topology*, Section 2.1, Corollary 2.14, for the homology obstruction to
contractibility of spheres.
-/

public section

open CategoryTheory Limits Metric Module

universe w

namespace TauCeti

/-- The unit sphere of a nontrivial finite-dimensional real normed space is not contractible,
including in ambient dimension one. -/
theorem not_contractibleSpace_sphere {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] :
    ¬ ContractibleSpace (sphere (0 : E) 1) := by
  intro h
  let := h
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (finrank_pos (R := ℝ) (M := E)).ne'
  let R := ModuleCat.of ℤ (ULift.{w} ℤ)
  let F := EuclideanSpace ℝ (ULift.{w} (Fin (n + 1)))
  have hEF : finrank ℝ E = finrank ℝ F :=
    hn.trans (finrank_euclideanSpace_ulift_fin (n + 1)).symm
  let e := reducedSingularHomologySphereIsoOfFinrankEq R hEF n ≪≫
    reducedSingularHomologySphereIso R
      ((EuclideanSpace.basisFun (ULift.{w} (Fin (n + 1))) ℝ).reindex Equiv.ulift)
  have hz : IsZero R :=
    (isZero_reducedSingularHomologyFunctor_of_contractibleSpace R
      (TopCat.of (sphere (0 : E) 1)) n).of_iso e.symm
  have : Subsingleton (ULift.{w} ℤ) := ModuleCat.isZero_iff_subsingleton.mp hz
  exact zero_ne_one (Subsingleton.elim (0 : ULift.{w} ℤ) 1)

end TauCeti
