/- GID: D5/S3/TotalVariation/FairBiasIntegralHomology
   generality: G
   mirror-B: D5/B/S3/TotalVariation/FairBiasIntegralHomology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reduced integral homology in degree zero and for column nullity one. -/
import D5.S3.Geometry.CompactWedgeFiniteFactor
import D5.S3.Geometry.FiniteComponentClosure.BasedJoin
import Mathlib.Analysis.Normed.Module.Connected
import D5.S3.TotalVariation.FairBiasSphericalWedge
import D5.S3.Topology.TauCeti.AlgebraicTopology.Singular.Reduced

open Set Topology Metric Module
open D5.S3.Geometry.FiniteConeUnionWedge
open D5.S3.Geometry.CompactWedgeFiniteFactor
open D5.S3.Geometry.FiniteComponentClosure
open D5.S3.Geometry.EuclideanSphereJoin
open scoped ContinuousMap

namespace D5.S3.TotalVariation.FairBiasIntegralHomology

noncomputable section

private theorem pathConnected {J : Type*} {Z : J → Type*} [∀ j, TopologicalSpace (Z j)]
    [∀ j, PathConnectedSpace (Z j)] (b : ∀ j, Z j) : PathConnectedSpace (FamilyWedge b) := by
  have h (x : FamilyWedge b) : Joined (base b) x := by
    refine Quotient.inductionOn x ?_
    rintro (u | ⟨j, x⟩)
    · cases u
      exact Joined.refl _
    · change Joined (base b) (point b j x)
      simpa only [point_base b j] using
        (PathConnectedSpace.joined (b j) x).map (point b j).continuous
  exact ⟨⟨base b⟩, fun x y => (h x).symm.trans (h y)⟩

private theorem stdSphere_pathConnected (d : ℕ) (hd : 0 < d) : PathConnectedSpace (StdSphere d) := by
  let e := EuclideanSpace.basisFun (Fin (d + 1)) ℝ
  have h : (1 : Cardinal) < Module.rank ℝ (EuclideanSpace ℝ (Fin (d + 1))) := by
    rw [rank_eq_card_basis e.toBasis, Fintype.card_fin]
    exact_mod_cast (by omega : 1 < d + 1)
  exact isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere h 0 (by norm_num : (0 : ℝ) ≤ 1))

private def twoPointModel : Bool ≃ₜ StdSphere 0 :=
  boolTwoPointHomeomorph.trans twoPointSphereHomeomorph

private def zeroWedgeEquiv {J : Type*} (b : J → StdSphere 0) :
    FamilyWedge b ≃ Unit ⊕ J := by
  classical
  let other (j : J) := twoPointModel (Bool.not (twoPointModel.symm (b j)))
  have other_ne (j : J) : other j ≠ b j := by
    intro h
    have he : Bool.not (twoPointModel.symm (b j)) = twoPointModel.symm (b j) :=
      twoPointModel.injective (h.trans (twoPointModel.apply_symm_apply (b j)).symm)
    cases hbool : twoPointModel.symm (b j) <;> simp [hbool] at he
  have other_eq (j : J) (x : StdSphere 0) (hx : x ≠ b j) : other j = x := by
    apply twoPointModel.symm.injective
    have hn : twoPointModel.symm x ≠ twoPointModel.symm (b j) := fun h =>
      hx (twoPointModel.symm.injective h)
    rw [show twoPointModel.symm (other j) = Bool.not (twoPointModel.symm (b j)) from
      twoPointModel.symm_apply_apply _]
    cases hb : twoPointModel.symm (b j) <;> cases ht : twoPointModel.symm x <;> simp_all
  let raw : Unit ⊕ (Σ _ : J, StdSphere 0) → Unit ⊕ J :=
    Sum.elim Sum.inl (fun z => if z.2 = b z.1 then Sum.inl () else Sum.inr z.1)
  let g : Unit ⊕ J → FamilyWedge b := Sum.elim (fun _ => base b) (fun j => point b j (other j))
  have hr (z : Unit ⊕ (Σ _ : J, StdSphere 0)) (hz : z ∈ basePoints b) : raw z = Sum.inl () := by
    rcases hz with rfl | ⟨j, rfl⟩
    · rfl
    · simp [raw]
  let f : FamilyWedge b → Unit ⊕ J :=
    Quotient.lift raw (by
      rintro z w (rfl | ⟨hz, hw⟩)
      · rfl
      · exact (hr z hz).trans (hr w hw).symm)
  refine ⟨f, g, ?_, ?_⟩
  · intro p
    refine Quotient.inductionOn p ?_
    rintro (u | ⟨j, x⟩)
    · cases u
      rfl
    · change g (if x = b j then Sum.inl () else Sum.inr j) = point b j x
      split_ifs with hx
      · rw [hx, point_base]
        rfl
      · exact congrArg (point b j) (other_eq j x hx)
  · rintro (u | j)
    · cases u
      rfl
    · change (if other j = b j then Sum.inl () else Sum.inr j) = _
      rw [ite_eq_right (other_ne j)]


section ZerothHomology

open CategoryTheory Limits AlgebraicTopology

universe w u v
variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

private theorem zeroWedgeDiscrete {J : Type w} (b : J → StdSphere 0) :
    DiscreteTopology (FamilyWedge b) := by
  let _ : DiscreteTopology (StdSphere 0) := twoPointModel.discreteTopology
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  apply isQuotientMap_quotient_mk'.isCoinducing.isOpen_preimage.mp
  exact isOpen_sum_iff.mpr ⟨isOpen_discrete _, isOpen_sigma_iff.mpr (fun _ => isOpen_discrete _)⟩

private def discreteComponents {X : Type w} [TopologicalSpace X] [DiscreteTopology X] :
    ZerothHomotopy X ≃ X :=
  (Equiv.ofBijective ZerothHomotopy.mk ⟨by
    intro _ _ he
    obtain ⟨p⟩ := Quotient.exact he
    exact (isPreconnected_range p.continuous).subsingleton
      ⟨0, p.source⟩ ⟨1, p.target⟩, ZerothHomotopy.mk_surjective⟩).symm

private def zeroWedgeComponents {J : Type w} (b : J → StdSphere 0) :
    {c : ZerothHomotopy (FamilyWedge b) // c ≠ ZerothHomotopy.mk (base b)} ≃ J := by
  letI := zeroWedgeDiscrete b
  let e := discreteComponents.trans (zeroWedgeEquiv b)
  have he : e (ZerothHomotopy.mk (base b)) = Sum.inl () := by
    change zeroWedgeEquiv b (discreteComponents (ZerothHomotopy.mk (base b))) = Sum.inl ()
    have hr : discreteComponents.symm (base b) = ZerothHomotopy.mk (base b) := rfl
    rw [← hr, Equiv.apply_symm_apply]
    rfl
  let step : {s : Unit ⊕ J // s ≠ Sum.inl ()} ≃ J := {
    toFun := fun s => match s with
      | ⟨Sum.inl u, h⟩ => (h (congrArg Sum.inl (Subsingleton.elim u ()))).elim
      | ⟨Sum.inr j, _⟩ => j
    invFun := fun j => ⟨Sum.inr j, Sum.inr_ne_inl⟩
    left_inv := by
      rintro ⟨u | j, h⟩
      · exact (h (congrArg Sum.inl (Subsingleton.elim u ()))).elim
      · rfl
    right_inv := fun _ => rfl }
  exact (e.subtypeEquiv (fun c => by
    change c ≠ ZerothHomotopy.mk (base b) ↔ e c ≠ Sum.inl ()
    rw [← he]
    exact not_congr e.injective.eq_iff.symm)).trans step

private def zeroWedgeH0 {J : Type w} (R : C) (b : J → StdSphere 0) :
    (TauCeti.reducedSingularHomologyFunctor R 0).obj (TopCat.of (FamilyWedge b)) ≅
      ∐ fun _ : J => R :=
  TauCeti.reducedSingularHomology₀Iso R (base b) ≪≫
    Sigma.whiskerEquiv (zeroWedgeComponents b) (fun _ => Iso.refl R)

private theorem zeroWedgeHigherVanishing {J : Type w} (R : C) (b : J → StdSphere 0)
    (k : ℕ) :
    IsZero ((TauCeti.reducedSingularHomologyFunctor R (k + 1)).obj
      (TopCat.of (FamilyWedge b))) := by
  let _ := zeroWedgeDiscrete b
  exact (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C (k + 1) R
    (TopCat.of (FamilyWedge b)) (Nat.succ_ne_zero k)).of_iso
    ((TauCeti.reducedSingularHomologySuccIso R k).app _)

private theorem positiveWedgeH0 {J : Type w} (R : C) (d : ℕ) (hd : 0 < d)
    (b : J → StdSphere d) :
    IsZero ((TauCeti.reducedSingularHomologyFunctor R 0).obj (TopCat.of (FamilyWedge b))) := by
  let _ := @pathConnected J (fun _ => StdSphere d) (fun _ => inferInstance)
    (fun _ => stdSphere_pathConnected d hd) b
  exact TauCeti.isZero_reducedSingularHomologyFunctor_zero R _

#print axioms zeroWedgeH0
#print axioms zeroWedgeHigherVanishing
#print axioms positiveWedgeH0

end ZerothHomology


section FairBias

open CategoryTheory Limits AlgebraicTopology
open D5.S3.Geometry.FiniteSimplicialJoin (Space)
open D5.S3.TotalVariation.FairBiasCriticalFacetCollapse
open D5.S3.TotalVariation.FairBiasLink
open D5.S3.TotalVariation.FairBiasRestriction
open D5.S3.TotalVariation.FairBiasSphericalWedge

universe u v
variable {A : Type u} {L : Type v} [AddCommGroup A] [Module (ZMod 2) A]
  [Finite A] [Fintype L] [LinearOrder (L × Bool)]

open scoped ContinuousMap

/-- The reduced zeroth group of the signed realization, and all its reduced groups
when the column family has nullity one. -/
theorem fairBiasZeroAndNullityOne (c : L → A) (h : (facets c).Nonempty) :
    let d := Fintype.card L - Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range c)) - 1
    let R := ModuleCat.of ℤ (ULift.{v} ℤ)
    let X := TopCat.of (Space (signedComplex c))
    (d = 0 →
      Nonempty ((TauCeti.reducedSingularHomologyFunctor R 0).obj X ≅
        ∐ fun _ : fullRestrictionFacets c => R) ∧
      ∀ k : ℕ, IsZero ((TauCeti.reducedSingularHomologyFunctor R (k + 1)).obj X)) ∧
    (0 < d → IsZero ((TauCeti.reducedSingularHomologyFunctor R 0).obj X)) := by
  let d := Fintype.card L - Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range c)) - 1
  let R := ModuleCat.of ℤ (ULift.{v} ℤ)
  obtain ⟨b, _, e, _, H, _, _, _⟩ := exists_spherical_wedge c h
  have hb : ∃ b' : fullRestrictionFacets c → StdSphere d,
      Nonempty (Space (signedComplex c) ≃ₕ FamilyWedge b') :=
    ⟨b, ⟨H.trans e.toHomotopyEquiv⟩⟩
  constructor
  · intro hz
    change d = 0 at hz
    rw [hz] at hb
    obtain ⟨b, ⟨E⟩⟩ := hb
    exact ⟨⟨E.reducedSingularHomologyIso R 0 ≪≫ zeroWedgeH0 R b⟩,
      fun k => (zeroWedgeHigherVanishing R b k).of_iso
        (E.reducedSingularHomologyIso R (k + 1))⟩
  · intro hd
    obtain ⟨b, ⟨E⟩⟩ := hb
    exact (positiveWedgeH0 R d hd b).of_iso (E.reducedSingularHomologyIso R 0)

#print axioms fairBiasZeroAndNullityOne

end FairBias

end
end D5.S3.TotalVariation.FairBiasIntegralHomology
