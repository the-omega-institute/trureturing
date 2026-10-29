import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
This file is a source port adapted from TauCetiProject/TauCeti at immutable
revision `5a01f5fe3621126cccf9ba22e700493cbc7b7156`, source path
`TauCeti/AlgebraicTopology/Singular/Basic.lean`. Changes: import paths are namespaced under
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
# Singular chain complexes

This module relates the singular-chain functor to the chain map induced by a map of singular
simplicial sets, and the singular homology functor to the simplicial homology map it induces.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] (R : C)

/-- The singular chain complex functor with coefficients in `R` sends a continuous map `f` to the
simplicial chain map induced by the singular simplicial map `TopCat.toSSet.map f`. -/
@[simp]
lemma singularChainComplexFunctor_obj_map {X Y : TopCat.{w}} (f : X ⟶ Y) :
    ((AlgebraicTopology.singularChainComplexFunctor C).obj R).map f =
      SSet.chainComplexMap (TopCat.toSSet.map f) R := rfl

/-- A coefficient morphism acts on singular chains by its simplicial chain map evaluated
at the singular simplicial set. -/
@[simp]
lemma singularChainComplexFunctor_map_app {R R' : C} (g : R ⟶ R') (X : TopCat.{w}) :
    ((AlgebraicTopology.singularChainComplexFunctor C).map g).app X =
      ((SSet.chainComplexFunctor C).map g).app (TopCat.toSSet.obj X) :=
  (rfl)

/-- The singular homology functor with coefficients in `R` sends a continuous map `f` to the
simplicial homology map induced by the singular simplicial map `TopCat.toSSet.map f`. -/
lemma singularHomologyFunctor_obj_map [CategoryWithHomology C] (n : ℕ) {X Y : TopCat.{w}}
    (f : X ⟶ Y) :
    ((AlgebraicTopology.singularHomologyFunctor C n).obj R).map f =
      SSet.homologyMap (TopCat.toSSet.map f) R n := rfl

end TauCeti
