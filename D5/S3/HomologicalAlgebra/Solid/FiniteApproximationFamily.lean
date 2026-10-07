/- GID: D5/S3/HomologicalAlgebra/Solid/FiniteApproximationFamily
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/FiniteApproximationFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.FiniteApproximation
import Mathlib.Topology.Category.LightProfinite.Sequence
import Mathlib.Topology.CompactOpen

/-!
The genuine continuous family (n,s) -> r_n(s), with infinity row s -> s,
for the compatible finite approximations of an arbitrary light profinite S.
Continuity is proved coordinatewise in the actual finite presentation: each
projected family is eventually the projection itself as a continuous map,
uniformly for all s. Empty, finite and infinite S are all allowed.
New proofs, Apache-2.0. Research construction: Juan Esteban Rodriguez Camargo,
Notes on Solid Geometry, Lemma 3.3.2.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightProfinite OnePoint Filter Topology

namespace CWSolid

def finiteApproximationFamilyDomain (S : LightProfinite) : LightProfinite :=
  LightProfinite.of (OnePoint ℕ × S)

/-- The projected family is eventually exactly constant in the function
space, so continuity requires no separate uniform convergence assertion. -/
def finiteApproximationCoordinateSequence (S : LightProfinite) (m : ℕ) :
    C(OnePoint ℕ, C(S, S.component m)) where
  toFun
    | ∞ => (S.proj m).hom.hom
    | OnePoint.some n => (finiteApproximation S n ≫ S.proj m).hom.hom
  continuous_toFun := by
    rw [OnePoint.continuous_iff_from_nat]
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ge_atTop m] with n hn
    exact congrArg (fun f : S ⟶ S.component m => f.hom.hom)
      (finiteApproximation_projLE S hn)

def finiteApproximationCoordinate (S : LightProfinite) (m : ℕ) :
    finiteApproximationFamilyDomain S ⟶ S.component m :=
  ConcreteCategory.ofHom
    ⟨fun x => finiteApproximationCoordinateSequence S m x.1 x.2,
      ContinuousMap.continuous_uncurry_of_continuous
        (finiteApproximationCoordinateSequence S m)⟩

def finiteApproximationFamilyCone (S : LightProfinite) : Cone S.diagram where
  pt := finiteApproximationFamilyDomain S
  π := {
    app := fun m => finiteApproximationCoordinate S m.unop
    naturality := by
      intro m n f
      simp only [Functor.const_obj_map, Category.id_comp]
      symm
      ext ⟨a, s⟩
      have h := S.asLimitCone.w f
      cases a using OnePoint.rec
      · change S.diagram.map f (S.proj m.unop s) = S.proj n.unop s
        exact ConcreteCategory.congr_hom h s
      · rename_i k
        change S.diagram.map f (S.proj m.unop (finiteApproximation S k s)) =
          S.proj n.unop (finiteApproximation S k s)
        exact ConcreteCategory.congr_hom h (finiteApproximation S k s) }

/-- The actual continuous morphism obtained from the limiting cone. -/
def finiteApproximationFamily (S : LightProfinite) :
    finiteApproximationFamilyDomain S ⟶ S :=
  S.asLimit.lift (finiteApproximationFamilyCone S)

theorem finiteApproximationFamily_proj (S : LightProfinite) (m : ℕ) :
    finiteApproximationFamily S ≫ S.proj m = finiteApproximationCoordinate S m :=
  S.asLimit.fac (finiteApproximationFamilyCone S) ⟨m⟩

def finiteApproximationFamilySlice (S : LightProfinite) (a : OnePoint ℕ) :
    S ⟶ finiteApproximationFamilyDomain S :=
  ConcreteCategory.ofHom ⟨fun s => (a, s), continuous_const.prodMk continuous_id⟩

theorem finiteApproximationFamily_finiteSlice (S : LightProfinite) (n : ℕ) :
    finiteApproximationFamilySlice S (n : OnePoint ℕ) ≫ finiteApproximationFamily S =
      finiteApproximation S n := by
  apply S.asLimit.hom_ext
  rintro ⟨m⟩
  change (finiteApproximationFamilySlice S (n : OnePoint ℕ) ≫ finiteApproximationFamily S) ≫
    S.proj m = finiteApproximation S n ≫ S.proj m
  rw [Category.assoc, finiteApproximationFamily_proj]
  ext s
  change S.proj m (finiteApproximation S n s) = S.proj m (finiteApproximation S n s)
  rfl

theorem finiteApproximationFamily_inftySlice (S : LightProfinite) :
    finiteApproximationFamilySlice S ∞ ≫ finiteApproximationFamily S = 𝟙 S := by
  apply S.asLimit.hom_ext
  rintro ⟨m⟩
  change (finiteApproximationFamilySlice S ∞ ≫ finiteApproximationFamily S) ≫
    S.proj m = 𝟙 S ≫ S.proj m
  rw [Category.assoc, finiteApproximationFamily_proj, Category.id_comp]
  ext s
  change S.proj m s = S.proj m s
  rfl

end CWSolid
