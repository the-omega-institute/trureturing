/- GID: D5/S3/Factorization/Mordell/SymmetricSquareAddition
   generality: G
   mirror-B: D5/B/S3/Factorization/Mordell/SymmetricSquareAddition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric-square coordinates satisfy homogeneous addition and subtraction. -/

/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license. The complete license and immutable sources are in
Library/ArithUnits/tauceti2026canonicalheight.md.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
public import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.LinearCombination

/-! The homogeneous addition-and-subtraction identity is supplied by
`WeierstrassCurve.Affine.Point.sym2x_add_sub_eq_addSubMap_sym2x` in the imported
`Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap`.
It includes infinity, inverses and doubling over every field. -/

public section

namespace WeierstrassCurve.Affine.Point

attribute [simp] sym2x_neg_left sym2x_neg_right

end WeierstrassCurve.Affine.Point
