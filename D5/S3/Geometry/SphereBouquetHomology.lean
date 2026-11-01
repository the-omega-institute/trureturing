/- GID: D5/S3/Geometry/SphereBouquetHomology
   generality: G
   mirror-B: D5/B/S3/Geometry/SphereBouquetHomology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact arbitrary sphere-wedge sources have torsion-free positive integral singular homology. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Geometry.HereditaryLexicographicProduct
import D5.S3.Geometry.FiniteVertexOpenStar
import D5.S3.Topology.SphereHomologyAllDegrees
import D5.S3.Topology.PointedWedgeHomology
import Mathlib.Algebra.Module.Torsion.Prod

/-! Actual finite sphere-bouquet homology and compact sourceSP torsion obstructions. -/

noncomputable section
open Set Topology CategoryTheory Limits AlgebraicTopology
open scoped ContinuousMap

namespace D5.S3.Geometry.SphereBouquetHomology
open CompactSphereNormalForm
open FiniteComponentClosure
open D5.S3.Topology

open private sphereSingletonBouquetHomeomorph from
  D5.S3.Geometry.FiniteComponentClosure.JoinModels
open private bouquetAppendHomeomorph from
  D5.S3.Geometry.FiniteComponentClosure.SelectedWedge
open private emptyBouquet_point
  bouquetVertex_face from
  D5.S3.Geometry.FiniteComponentClosure.Models

universe v

private abbrev NativeBouquet (b : List PositiveDimension) :=
  FiniteSimplicialJoin.Space (bouquetComplex b)

section Coefficients
variable {k : Type} [Ring k]
    (M : ModuleCat k) [Module.IsTorsionFree k M]

/-- Finite native positive bouquets have torsion-free actual singular homology
in every positive degree, by induction using actual open MV covers. -/
private theorem native_torsionFree (b : List PositiveDimension) (r : ℕ) :
    Module.IsTorsionFree k
      (((singularHomologyFunctor (ModuleCat k) (r + 1)).obj M).obj
        (TopCat.of (NativeBouquet b))) := by
  induction b with
  | nil =>
      letI : Nonempty (NativeBouquet []) := ⟨bouquetPoint []⟩
      letI : Subsingleton (NativeBouquet []) :=
        ⟨fun x y => (emptyBouquet_point x).trans (emptyBouquet_point y).symm⟩
      letI : ContractibleSpace (NativeBouquet []) := inferInstance
      letI : Subsingleton
          (((singularHomologyFunctor (ModuleCat k) (r + 1)).obj M).obj
            (TopCat.of (NativeBouquet []))) :=
        ModuleCat.isZero_iff_subsingleton.mp
          (TauCeti.isZero_singularHomologyFunctor_of_contractibleSpace M
            (TopCat.of (NativeBouquet [])) (Nat.succ_ne_zero r))
      infer_instance
  | cons d b ih =>
      let X := NativeBouquet [d]
      let Y := NativeBouquet b
      let a : X := bouquetPoint [d]
      let c : Y := bouquetPoint b
      let sphereEquiv : X ≃ₜ EuclideanSphereJoin.StdSphere d.val :=
        (sphereSingletonBouquetHomeomorph d).symm.trans (sphereHomeomorph d.val)
      letI : Module.IsTorsionFree k
          (((singularHomologyFunctor (ModuleCat k) (r + 1)).obj M).obj
            (TopCat.of (EuclideanSphereJoin.StdSphere d.val))) :=
        SphereHomologyAllDegrees.isTorsionFree_singularHomology_sphere M
          (EuclideanSpace.basisFun (Fin (d.val + 1)) ℝ) (r + 1) (Nat.succ_pos r)
      let eS :
          (((singularHomologyFunctor (ModuleCat k) (r + 1)).obj M).obj (TopCat.of X)) ≃ₗ[k]
          (((singularHomologyFunctor (ModuleCat k) (r + 1)).obj M).obj
            (TopCat.of (EuclideanSphereJoin.StdSphere d.val))) :=
        (sphereEquiv.toHomotopyEquiv.reducedSingularHomologyIso M (r + 1)).toLinearEquiv
      letI : Module.IsTorsionFree k
          (((singularHomologyFunctor (ModuleCat k) (r + 1)).obj M).obj (TopCat.of X)) :=
        Function.Injective.moduleIsTorsionFree eS eS.injective (fun n z => eS.map_smul n z)
      letI : Module.IsTorsionFree k
          (((singularHomologyFunctor (ModuleCat k) (r + 1)).obj M).obj (TopCat.of Y)) := ih
      let A := FiniteVertexOpenStar.star (bouquetComplex [d]) none
      let B := FiniteVertexOpenStar.star (bouquetComplex b) none
      have hA : IsOpen A := FiniteVertexOpenStar.isOpen_star _ _
      have hB : IsOpen B := FiniteVertexOpenStar.isOpen_star _ _
      have ha : a ∈ A := FiniteVertexOpenStar.vertex_mem_star _ _ (bouquetVertex_face [d])
      have hc : c ∈ B := FiniteVertexOpenStar.vertex_mem_star _ _ (bouquetVertex_face b)
      let H := FiniteVertexOpenStar.contraction _ _ (bouquetVertex_face [d])
      let K := FiniteVertexOpenStar.contraction _ _ (bouquetVertex_face b)
      let E := PointedWedgeHomology.homologyIso a c hA hB ha hc H K M
        (r + 1) (Nat.succ_pos r)
      let F := ((singularHomologyFunctor (ModuleCat k) (r + 1)).obj M).mapIso
        (TopCat.isoOfHomeo (X := TopCat.of (FiniteConeUnionWedge.Wedge a c))
          (Y := TopCat.of (NativeBouquet ([d] ++ b))) (bouquetAppendHomeomorph [d] b))
      let L := (F.symm ≪≫ E.symm ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv
      change Module.IsTorsionFree k
        (((singularHomologyFunctor (ModuleCat k) (r + 1)).obj M).obj
          (TopCat.of (NativeBouquet ([d] ++ b))))
      exact Function.Injective.moduleIsTorsionFree L L.injective (fun n z => L.map_smul n z)

/-- The general finite positive-bouquet theorem. The bouquet is the literal
FamilyWedge quotient of the actual standard spheres. The empty list is a point;
q is unrestricted and no relation between q and the sphere dimensions is assumed. -/
theorem finite_bouquet_torsionFree (b : List PositiveDimension)
    (q : ℕ) (hq : 1 ≤ q) :
    Module.IsTorsionFree k
      (((singularHomologyFunctor (ModuleCat k) q).obj M).obj (TopCat.of (Bouquet b))) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  letI := native_torsionFree M b r
  let E := (((singularHomologyFunctor (ModuleCat k) (r + 1)).obj M).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of (NativeBouquet b))
      (Y := TopCat.of (Bouquet b)) (nativeBouquetHomeomorph b))).symm.toLinearEquiv
  exact Function.Injective.moduleIsTorsionFree E E.injective (fun n z => E.map_smul n z)

private def sigmaFinSucc {m : ℕ} (Z : Fin (m + 1) → Type)
    [∀ i, TopologicalSpace (Z i)] :
    (Σ i, Z i) ≃ₜ Z 0 ⊕ (Σ i : Fin m, Z i.succ) where
  toFun z := Fin.cases (fun x : Z 0 => Sum.inl x)
    (fun i (x : Z i.succ) => Sum.inr ⟨i, x⟩) z.1 z.2
  invFun := Sum.elim (Sigma.mk 0) (fun z => ⟨z.1.succ, z.2⟩)
  left_inv := by
    rintro ⟨i, x⟩
    revert x
    refine Fin.cases ?_ (fun j => ?_) i <;> intro x <;> rfl
  right_inv := by rintro (x | ⟨i, x⟩) <;> rfl
  continuous_toFun := continuous_sigma_iff.mpr (by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_inl
    · change Continuous (fun x : Z j.succ =>
        (Sum.inr (Sigma.mk j x) : Z 0 ⊕ (Σ i : Fin m, Z i.succ)))
      exact continuous_inr.comp
        (@continuous_sigmaMk (Fin m) (fun i : Fin m => Z i.succ)
          (fun i => inferInstance) j))
  continuous_invFun := continuous_sigmaMk.sumElim
    (continuous_sigma_iff.mpr (fun i => continuous_sigmaMk))

/-- The actual finite outer coproduct is handled by open disjoint-sum MV;
size zero gives the empty space, rather than the point bouquet. -/
theorem finite_model_torsionFree {m : ℕ} (b : Fin m → List PositiveDimension)
    (q : ℕ) (hq : 1 ≤ q) :
    Module.IsTorsionFree k
      (((singularHomologyFunctor (ModuleCat k) q).obj M).obj (TopCat.of (Model b))) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  induction m with
  | zero =>
      letI : IsEmpty (Model b) := ⟨fun z => Fin.elim0 z.1⟩
      letI : Subsingleton
          (((singularHomologyFunctor (ModuleCat k) (r + 1)).obj M).obj
            (TopCat.of (Model b))) :=
        ModuleCat.isZero_iff_subsingleton.mp
          (TauCeti.isZero_reducedSingularHomologyFunctor_of_isEmpty M
            (TopCat.of (Model b)) (r + 1))
      infer_instance
  | succ m ih =>
      letI := finite_bouquet_torsionFree M (b 0) (r + 1) (by omega)
      letI := ih (fun i => b i.succ)
      let F := ((singularHomologyFunctor (ModuleCat k) (r + 1)).obj M).mapIso
        (TopCat.isoOfHomeo (X := TopCat.of (Model b))
          (Y := TopCat.of (Bouquet (b 0) ⊕ Model (fun i : Fin m => b i.succ)))
          (sigmaFinSucc (fun i => Bouquet (b i))))
      let E := OpenCoverHomology.sumIso M (Bouquet (b 0))
        (Model (fun i : Fin m => b i.succ)) (r + 1) (Nat.succ_pos r)
      let L := (F ≪≫ E.symm ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv
      exact Function.Injective.moduleIsTorsionFree L L.injective (fun n z => L.map_smul n z)

/-- Arbitrary original index families and original sphere basepoints, with
no finiteness or positivity restriction on d. Compactness is consumed only
by the existing actual compact normalization equivalence. -/
theorem compact_wedge_torsionFree {X : Type} [TopologicalSpace X] [CompactSpace X]
    {J : Type v} (d : J → ℕ) (p : ∀ j, EuclideanSphereJoin.StdSphere (d j))
    (e : X ≃ₕ CompactWedgeFiniteFactor.FamilyWedge p)
    (q : ℕ) (hq : 1 ≤ q) :
    Module.IsTorsionFree k
      (((singularHomologyFunctor (ModuleCat k) q).obj M).obj (TopCat.of X)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  let N := compactWedgeModel d p e
  letI := finite_model_torsionFree M N.bouquets (r + 1) (by omega)
  let L :
      (((singularHomologyFunctor (ModuleCat k) (r + 1)).obj M).obj (TopCat.of X)) ≃ₗ[k]
      (((singularHomologyFunctor (ModuleCat k) (r + 1)).obj M).obj
        (TopCat.of (Model N.bouquets))) :=
    (N.equivalence.reducedSingularHomologyIso M (r + 1)).toLinearEquiv
  exact Function.Injective.moduleIsTorsionFree L L.injective (fun n z => L.map_smul n z)

end Coefficients

/-- Actual compact sourceSP spaces have torsion-free positive-degree integral
singular homology. J in sourceSP ranges over Type v without any finiteness
assumption; original basepoints and S⁰ factors are processed by the existing
compactWedgeModel. The homology carrier is Mathlib's singularHomologyFunctor. -/
theorem compact_sourceSP_torsionFree {X : Type} [TopologicalSpace X] [CompactSpace X]
    (h : HereditaryLexicographicProduct.sourceSP.{0, v} X)
    (q : ℕ) (hq : 1 ≤ q) :
    Module.IsTorsionFree ℤ
      (((singularHomologyFunctor (ModuleCat ℤ) q).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of X)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  rcases h with h | ⟨J, d, p, ⟨e⟩⟩
  · letI := h
    letI : Subsingleton
        (((singularHomologyFunctor (ModuleCat ℤ) (r + 1)).obj (ModuleCat.of ℤ ℤ)).obj
          (TopCat.of X)) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (TauCeti.isZero_singularHomologyFunctor_of_contractibleSpace
          (ModuleCat.of ℤ ℤ) (TopCat.of X) (Nat.succ_ne_zero r))
    infer_instance
  · exact compact_wedge_torsionFree (ModuleCat.of ℤ ℤ) d p e (r + 1) (by omega)

/-- The explicit original-obstruction telescope: every nonzero integer acts
injectively on every positive-degree integral actual singular homology group
of every compact sourceSP space, with arbitrary original sphere family. -/
theorem compact_sourceSP_smul_eq_zero {X : Type} [TopologicalSpace X] [CompactSpace X]
    (h : HereditaryLexicographicProduct.sourceSP.{0, v} X)
    (q : ℕ) (hq : 1 ≤ q) (n : ℤ) (hn : n ≠ 0)
    (z : (((singularHomologyFunctor (ModuleCat ℤ) q).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of X))) (hz : n • z = 0) : z = 0 := by
  letI := compact_sourceSP_torsionFree h q hq
  apply (smul_eq_zero_iff_right hn).mp
  simpa only [Int.cast_id] using (Int.cast_smul_eq_zsmul ℤ n z).trans hz

set_option pp.universes true
#check @SphereHomologyAllDegrees.isTorsionFree_singularHomology_sphere
#check @OpenCoverHomology.inclusionIso
#check @PointedWedgeHomology.homologyIso
#check @finite_bouquet_torsionFree
#check @finite_model_torsionFree
#check @compact_wedge_torsionFree
#check @compact_sourceSP_torsionFree
#check @compact_sourceSP_smul_eq_zero
#print axioms finite_bouquet_torsionFree
#print axioms finite_model_torsionFree
#print axioms compact_wedge_torsionFree
#print axioms compact_sourceSP_torsionFree
#print axioms compact_sourceSP_smul_eq_zero

end D5.S3.Geometry.SphereBouquetHomology
