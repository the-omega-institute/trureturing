/- GID: D5/S1/Solenoid/SingularHomology
   generality: I
   mirror-B: D5/B/S1/Solenoid/SingularHomology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Genuine simplex lifts compute positive solenoid singular homology. -/

import D5.S1.Dynamics.UniversalSolenoidCoordinate
import D5.S1.Solenoid.PathOrbitClassification
import D5.S1.Solenoid.RealFlowInjectivity
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Positive singular homology of the universal solenoid -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace D5.S1.Solenoid.SingularHomology

open Set Function CategoryTheory CategoryTheory.Limits AlgebraicTopology Convexity
open D5.S1.Dynamics
open D5.S1.Solenoid.PathOrbitClassification
open D5.S1.Solenoid.RealFlowInjectivity

private theorem kernel_motion_constant {A : Type u} [TopologicalSpace A]
    [PreconnectedSpace A] (motion : C(A, UniversalSolenoid))
    (hmotion : ∀ a, UniversalSolenoid.projection (motion a) = 0) (a b : A) :
    motion a = motion b := by
  apply Subtype.ext
  funext m
  let coordinate : A → AddCircle (1 : ℝ) := fun x => (motion x).1 m
  have hc : Continuous coordinate :=
    ((continuous_apply m).comp continuous_subtype_val).comp motion.continuous
  have hm : MapsTo coordinate univ {x : AddCircle (1 : ℝ) | m.1 • x = 0} := by
    intro x _
    exact UniversalSolenoid.nsmul_coordinate_eq_zero (hmotion x) m
  exact isPreconnected_univ.constant_of_mapsTo
    (AddCircle.finite_torsion (1 : ℝ) m.2).isDiscrete hc.continuousOn hm
    (mem_univ a) (mem_univ b)

/-- A map from a simply connected, locally path-connected source has a unique
continuous real parameter relative to its value at a chosen basepoint. This is
a lifting statement on the source, not an inverse-continuity assertion for an
entire real-flow orbit in the solenoid. -/
theorem exists_unique_normalized_lift {A : Type u} [TopologicalSpace A]
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    (f : C(A, UniversalSolenoid)) (a₀ : A) :
    ∃! r : C(A, ℝ), r a₀ = 0 ∧
      ∀ a, f a = UniversalSolenoid.realFlow (r a) + f a₀ := by
  let visible : C(A, AddCircle (1 : ℝ)) :=
    ⟨fun a => UniversalSolenoid.projection (f a - f a₀),
      UniversalSolenoid.continuous_projection.comp
        (f.continuous.sub continuous_const)⟩
  rcases (AddCircle.isCoveringMap_coe (1 : ℝ)).existsUnique_continuousMap_lifts
      visible a₀ 0 (by simp [visible]) with ⟨r, hr, _⟩
  let difference : C(A, UniversalSolenoid) :=
    ⟨fun a => f a - UniversalSolenoid.realFlow (r a) - f a₀,
      (f.continuous.sub (UniversalSolenoid.continuous_realFlow.comp r.continuous)).sub
        continuous_const⟩
  have hd : ∀ a, UniversalSolenoid.projection (difference a) = 0 := by
    intro a
    have hlift := congrFun hr.2 a
    change (r a : AddCircle (1 : ℝ)) =
      UniversalSolenoid.projection (f a - f a₀) at hlift
    change UniversalSolenoid.projection
      (f a - UniversalSolenoid.realFlow (r a) - f a₀) = 0
    rw [map_sub, map_sub, UniversalSolenoid.projection_realFlow, hlift, map_sub]
    abel
  have hzero (a : A) : difference a = 0 := by
    rw [kernel_motion_constant difference hd a a₀]
    simp [difference, hr.1, UniversalSolenoid.realFlow_zero]
  have hreconstruct (a : A) :
      f a = UniversalSolenoid.realFlow (r a) + f a₀ := by
    apply sub_eq_zero.mp
    calc
      f a - (UniversalSolenoid.realFlow (r a) + f a₀) = difference a := by
        dsimp [difference]
        abel
      _ = 0 := hzero a
  refine ⟨r, ⟨hr.1, hreconstruct⟩, ?_⟩
  intro other hother
  ext a
  apply realFlow_injective
  apply add_right_cancel (b := f a₀)
  rw [← hother.2 a, ← hreconstruct a]

/- The topology here is deliberately discrete. The quotient topology on
`ZerothHomotopy UniversalSolenoid` is not used for this resolution. -/
private structure ComponentLabel where
  val : ZerothHomotopy UniversalSolenoid

private instance : TopologicalSpace ComponentLabel := ⊥

private instance : DiscreteTopology ComponentLabel := ⟨rfl⟩

private abbrev ComponentSpace : TopCat := TopCat.of ComponentLabel

private def representative (b : ComponentSpace) : UniversalSolenoid := Quotient.out b.val

private def orbitMap : C(ComponentSpace × ℝ, UniversalSolenoid) where
  toFun p := UniversalSolenoid.realFlow p.2 + representative p.1
  continuous_toFun := (UniversalSolenoid.continuous_realFlow.comp continuous_snd).add
    ((continuous_of_discreteTopology : Continuous representative).comp continuous_fst)

private theorem orbit_map_component (p : ComponentSpace × ℝ) :
    ZerothHomotopy.mk (orbitMap p) = p.1.val := by
  have h : Joined (representative p.1) (orbitMap p) :=
    (path_joined_iff_real_flow_orbit _ _).2 ⟨p.2, rfl⟩
  exact (Quotient.sound h).symm.trans (Quotient.out_eq p.1.val)

private theorem orbit_map_bijective : Bijective orbitMap := by
  constructor
  · rintro ⟨b, t⟩ ⟨c, s⟩ h
    have hbc : b = c := congrArg ComponentLabel.mk ((orbit_map_component (b, t)).symm.trans
      ((congrArg ZerothHomotopy.mk h).trans (orbit_map_component (c, s))))
    subst c
    exact Prod.ext rfl (realFlow_injective (add_right_cancel h))
  · intro x
    let b : ComponentSpace := ⟨ZerothHomotopy.mk x⟩
    have h : Joined (representative b) x := Quotient.exact (Quotient.out_eq b.val)
    obtain ⟨t, ht⟩ := (path_joined_iff_real_flow_orbit _ _).1 h
    exact ⟨(b, t), ht.symm⟩

private theorem orbit_map_lifts {A : Type u} [TopologicalSpace A]
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    (f : C(A, UniversalSolenoid)) (a₀ : A) :
    ∃ g : C(A, ComponentSpace × ℝ), orbitMap.comp g = f := by
  obtain ⟨r, hr, _⟩ := exists_unique_normalized_lift f a₀
  obtain ⟨⟨b, t⟩, hbase⟩ := orbit_map_bijective.2 (f a₀)
  let g : C(A, ComponentSpace × ℝ) :=
    ⟨fun a => (b, r a + t), continuous_const.prodMk (r.continuous.add continuous_const)⟩
  refine ⟨g, ?_⟩
  apply ContinuousMap.ext
  intro a
  change UniversalSolenoid.realFlow (r a + t) + representative b = f a
  rw [UniversalSolenoid.realFlow_add, add_assoc,
    show UniversalSolenoid.realFlow t + representative b = f a₀ from hbase]
  exact (hr.2 a).symm

/- The singular functor uses the new `Convexity.StdSimplex` carrier. Its
embedding into finite real coordinate space transports the existing convex-set
contractibility and local path-connectedness results to that carrier. -/
private def simplexCoordinateHomeomorph (ι : Type) [Fintype ι] :
    StdSimplex ℝ ι ≃ₜ (stdSimplex ℝ ι) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).toHomeomorph.trans
    (Homeomorph.setCongr (by
      rw [StdSimplex.range_toFun_comp_weights]
      ext f
      simp [stdSimplex]))

private instance simplex_simply_connected (n : ℕ) :
    SimplyConnectedSpace (StdSimplex ℝ (Fin (n + 1))) := by
  letI : ContractibleSpace (stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ _).contractibleSpace
      ⟨_, single_mem_stdSimplex ℝ (0 : Fin (n + 1))⟩
  letI : ContractibleSpace (StdSimplex ℝ (Fin (n + 1))) :=
    (simplexCoordinateHomeomorph _).contractibleSpace_iff.mpr inferInstance
  infer_instance

private instance simplex_locally_path_connected (n : ℕ) :
    LocallyPathConnectedSpace (StdSimplex ℝ (Fin (n + 1))) := by
  letI : LocallyPathConnectedSpace (stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ _).locallyPathConnectedSpace
  exact (simplexCoordinateHomeomorph _).symm.locallyPathConnectedSpace

/- This is an isomorphism of the actual singular simplicial sets: naturality
is already the naturality of `TopCat.toSSet.map` for the continuous map q.
Only its componentwise bijectivity needs proof, using genuine simplex lifts. -/
private instance orbit_map_singular_is_iso :
    IsIso (TopCat.toSSet.map (TopCat.ofHom orbitMap)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  constructor
  · intro f g h
    apply (TopCat.toSSetObjEquiv _ n).injective
    apply ContinuousMap.ext
    intro x
    apply orbit_map_bijective.1
    exact congrArg (fun s => TopCat.toSSetObjEquiv _ n s x) h
  · intro s
    let f := TopCat.toSSetObjEquiv (TopCat.of UniversalSolenoid) n s
    obtain ⟨g, hg⟩ := orbit_map_lifts f (StdSimplex.single (0 : Fin (n.unop.len + 1)))
    refine ⟨(TopCat.toSSetObjEquiv _ n).symm g, ?_⟩
    apply (TopCat.toSSetObjEquiv _ n).injective
    change orbitMap.comp g = f
    exact hg

private def componentProjection :
    TopCat.of (ComponentSpace × ℝ) ⟶ ComponentSpace :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

private def componentSection :
    ComponentSpace ⟶ TopCat.of (ComponentSpace × ℝ) :=
  TopCat.ofHom ⟨fun b => (b, 0), continuous_id.prodMk continuous_const⟩

private def contractRealCoordinate :
    TopCat.Homotopy (𝟙 (TopCat.of (ComponentSpace × ℝ)))
      (componentProjection ≫ componentSection) where
  toFun p := (p.2.1, (1 - (p.1 : ℝ)) * p.2.2)
  continuous_toFun := by fun_prop
  map_zero_left := by intro p; simp
  map_one_left := by intro p; simp [componentProjection, componentSection]

/-- Every positive-degree ordinary singular homology object of the universal
solenoid, with integral coefficients, is zero. The proof resolves all singular
simplices by continuous real lifts; it does not replace the solenoid topology
by the finer disjoint union topology. -/
theorem singular_homology_positive_is_zero (n : ℕ) (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor (ModuleCat ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of UniversalSolenoid)) := by
  let R := ModuleCat.of ℤ ℤ
  let F := (singularHomologyFunctor (ModuleCat ℤ) n).obj R
  have hB : IsZero (F.obj ComponentSpace) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℤ) n R ComponentSpace hn
  have hX : IsZero (F.obj (TopCat.of (ComponentSpace × ℝ))) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    have h := contractRealCoordinate.congr_homologyMap_singularChainComplexFunctor R n
    change F.map (𝟙 _) = F.map (componentProjection ≫ componentSection) at h
    rw [F.map_id, F.map_comp] at h
    calc
      𝟙 _ = F.map componentProjection ≫ F.map componentSection := h
      _ = 0 := by
        rw [hB.eq_of_tgt (F.map componentProjection) 0, zero_comp]
  haveI : IsIso (F.map (TopCat.ofHom orbitMap)) := by
    change IsIso ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) _ n).map
      (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj R).map
        (TopCat.toSSet.map (TopCat.ofHom orbitMap))))
    infer_instance
  exact hX.of_iso (asIso (F.map (TopCat.ofHom orbitMap))).symm

#print axioms singular_homology_positive_is_zero

end D5.S1.Solenoid.SingularHomology
