/- GID: D5/S3/HomologicalAlgebra/GraphCycleModuleCat
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/GraphCycleModuleCat
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/ModuleCat, arXiv:0910.5634]
   utility: none
   digest: The binary ModuleCat homology of a finite graph is its concrete cycle space. -/

import D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Projection

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
namespace D5.S3.HomologicalAlgebra.GraphCycleModuleCat

open CategoryTheory
open D5.S3.Fourier.CharacterSelection
open D5.S3.Fourier.CharacterSelection.BinaryCharacterCodeDuality
open D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace
open SimpleGraph

noncomputable def graphCycleDifferential {V : Type u} (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    (G.edgeSet → ZMod 2) →ₗ[ZMod 2] Module.Dual (ZMod 2) (V → ZMod 2) :=
  Fintype.linearCombination (ZMod 2) (endpointCharacters G)

noncomputable def graphCycleComplex {V : Type u} (G : SimpleGraph V)
    [Fintype G.edgeSet] : ShortComplex (ModuleCat.{u} (ZMod 2)) :=
  ShortComplex.moduleCatMk
    (0 : (ULift.{u} (Fin 0) → ZMod 2) →ₗ[ZMod 2] (G.edgeSet → ZMod 2))
    (graphCycleDifferential G) (by ext x; simp)

universe v w

noncomputable def moduleCatIsoOfLinearEquiv {R : Type w} [Ring R]
    {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (e : X ≃ₗ[R] Y) : ModuleCat.of R X ≅ ModuleCat.of R Y :=
  { hom := ModuleCat.ofHom e.toLinearMap
    inv := ModuleCat.ofHom e.symm.toLinearMap
    hom_inv_id := by ext; simp
    inv_hom_id := by ext; simp }

noncomputable def quotientKernelIso {V : Type u} (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    (graphCycleComplex G).moduleCatLeftHomologyData.H ≅
      ModuleCat.of (ZMod 2) (LinearMap.ker (graphCycleComplex G).g.hom) := by
  let K := LinearMap.ker (graphCycleComplex G).g.hom
  let f := (graphCycleComplex G).moduleCatToCycles
  have hf : LinearMap.range f = ⊥ := by
    apply (LinearMap.range_eq_bot).2
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (0 : (graphCycleComplex G).X₁ →ₗ[ZMod 2] (G.edgeSet → ZMod 2)) x = 0
    simp
  have hc : IsCompl (LinearMap.range f) (⊤ : Submodule (ZMod 2) K) := by
    rw [hf]
    exact isCompl_bot_top
  let q : (K ⧸ LinearMap.range f) ≃ₗ[ZMod 2] K :=
    (Submodule.quotientEquivOfIsCompl _ _ hc).trans Submodule.topEquiv
  exact moduleCatIsoOfLinearEquiv q

/-- The ordinary binary one-dimensional graph chain complex has homology equal to its
concrete binary cycle space.  This is the finite-coefficient form of the graph homology/cycle
space correspondence; the `ModuleCat` object records the categorical homology layer. -/
noncomputable def graphCycleHomologyIso {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [Fintype G.ConnectedComponent] :
    (graphCycleComplex G).homology ≅
      ModuleCat.of (ZMod 2) (simpleCycleSpace G) := by
  have hcycle : simpleCycleSpace G =
      LinearMap.ker (graphCycleDifferential G) := by
    simpa [graphCycleDifferential, characterRelationSpace] using
      (finite_graph_cycle_space G).1.1
  let eK : LinearMap.ker (graphCycleDifferential G) ≃ₗ[ZMod 2] simpleCycleSpace G :=
    LinearEquiv.ofEq _ _ hcycle.symm
  let eS : (graphCycleComplex G).moduleCatLeftHomologyData.H ≅
      ModuleCat.of (ZMod 2) (LinearMap.ker (graphCycleComplex G).g.hom) := quotientKernelIso G
  have hker : LinearMap.ker (graphCycleComplex G).g.hom =
      LinearMap.ker (graphCycleDifferential G) := by rfl
  have hcycle' : simpleCycleSpace G = LinearMap.ker (graphCycleComplex G).g.hom :=
    hcycle.trans hker.symm
  let eK' : LinearMap.ker (graphCycleComplex G).g.hom ≃ₗ[ZMod 2] simpleCycleSpace G :=
    LinearEquiv.ofEq _ _ hcycle'.symm
  exact ((graphCycleComplex G).moduleCatHomologyIso ≪≫ eS) ≪≫ moduleCatIsoOfLinearEquiv eK'

end D5.S3.HomologicalAlgebra.GraphCycleModuleCat
