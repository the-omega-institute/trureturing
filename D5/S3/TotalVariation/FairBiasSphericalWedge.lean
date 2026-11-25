/- GID: D5/S3/TotalVariation/FairBiasSphericalWedge
   generality: G
   mirror-B: D5/B/S3/TotalVariation/FairBiasSphericalWedge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The retained fair-bias core collapses to the basepoint of a wedge of spheres. -/
import D5.S3.TotalVariation.FairBiasFacetQuotient
import D5.S3.Geometry.CompactWedgeFiniteFactor
import D5.S3.Geometry.FiniteSimplexBoundarySphere
import D5.S3.Geometry.FiniteComponentClosure.BasedJoin
import Mathlib.Analysis.Convex.Contractible

/-! The original fair-bias link maps to the sphere wedge by its core quotient. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.TotalVariation.FairBiasSphericalWedge

open Set Topology

open D5.S3.Geometry
open D5.S3.Geometry.FiniteComponentClosure
open D5.S3.Geometry.FiniteConeCollapse
open D5.S3.Geometry.FiniteConeUnionWedge
open D5.S3.Geometry.FiniteSimplicialJoin (Space)
open D5.S3.TotalVariation.FairBiasCriticalFacetCollapse
open D5.S3.TotalVariation.FairBiasFacetQuotient
open D5.S3.TotalVariation.FairBiasLink
open D5.S3.TotalVariation.FairBiasRestriction

open scoped ContinuousMap

private theorem simplexOn_realization {V : Type*} [Fintype V] [DecidableEq V]
    (face : Finset V) (hne : face.Nonempty) :
    realization (simplexOn face) = faceSimplex face := by
  ext x
  rw [realization_mem_iff]
  constructor
  · rintro ⟨s, ⟨_, hsub⟩, hx⟩
    exact ⟨hx.1, hx.2.1, fun v hv => hx.2.2 v (fun h => hv (hsub h))⟩
  · intro hx
    exact ⟨face, ⟨hne, Finset.Subset.refl _⟩, hx⟩

private theorem simplexOn_contractible {V : Type*} [Fintype V] [DecidableEq V]
    (face : Finset V) (hne : face.Nonempty) : ContractibleSpace (Space (simplexOn face)) := by
  have hRealization := simplexOn_realization face hne
  have hConvex : Convex ℝ (realization (simplexOn face)) := by
    rw [hRealization, faceSimplex_eq_convexHull]
    exact convex_convexHull ℝ _
  have hNonempty : (realization (simplexOn face)).Nonempty := by
    rw [hRealization, faceSimplex_eq_convexHull]
    obtain ⟨v, hv⟩ := hne
    exact ⟨Pi.single v 1, subset_convexHull ℝ _ ⟨v, hv, rfl⟩⟩
  exact hConvex.contractibleSpace hNonempty

private theorem collapse_contractible_subcomplex {V : Type*} [Fintype V] [DecidableEq V]
    (K C : PreAbstractSimplicialComplex V) (hCK : C ≤ K) (a : V)
    (ha : ({a} : Finset V) ∈ C) [ContractibleSpace (Space C)] :
    ∃ H : Space K ≃ₕ Collapse (D5.S3.Geometry.FiniteSubcomplexCylinder.Subspace K C),
      H.toFun = collapseMap (D5.S3.Geometry.FiniteSubcomplexCylinder.Subspace K C) := by
  rw [← sup_eq_left.mpr hCK]
  let hOverlap : K ⊓ C ≤ C := inf_le_right
  let P := finiteConeCover K C C a a (hCK ha) ha ha ha hOverlap
  obtain ⟨e, he⟩ := contractible_cover_equivalence K C C a a (hCK ha) ha ha ha
    le_sup_right hOverlap
  refine ⟨e.trans P.quotientWedgeHomeomorph.toHomotopyEquiv, ?_⟩
  apply ContinuousMap.ext
  intro x
  change P.quotientWedgeHomeomorph (e.toFun x) = _
  rw [show e.toFun = P.quotientWedgeHomeomorph.symm.toHomotopyEquiv.toFun.comp
      (collapseMap (D5.S3.Geometry.FiniteSubcomplexCylinder.Subspace (K ⊔ C) C)) from he]
  exact P.quotientWedgeHomeomorph.apply_symm_apply _

universe coreA coreL
variable {A : Type coreA} {L : Type coreL} [AddCommGroup A] [Module (ZMod 2) A]
  [Finite A] [Fintype L] [LinearOrder (L × Bool)]

private theorem exists_core_collapse_equiv (c : L → A) (h : (facets c).Nonempty) :
    ∃ H : Space (signedComplex c) ≃ₕ Collapse (coreSet c),
      H.toFun = collapseMap (coreSet c) := by
  let _ : DecidableEq (L × Bool) := LinearOrder.toDecidableEq
  obtain ⟨B, hB, _, ⟨S⟩⟩ := exists_collapse_to_first_facet c h
  have hBne := ((signedComplex c).isRelLowerSet_faces (mem_facets.mp hB).1).1
  let _ := simplexOn_contractible B hBne
  let _ : ContractibleSpace (Space (retainedComplex c)) := S.collapseEquiv.contractibleSpace
  obtain ⟨v, hv⟩ := hBne
  have hvertex : ({v} : Finset (L × Bool)) ∈ retainedComplex c :=
    S.monotone ⟨Finset.singleton_nonempty _, Finset.singleton_subset_iff.mpr hv⟩
  exact collapse_contractible_subcomplex (signedComplex c) (retainedComplex c)
    (fun _ hs => hs.1) v hvertex

private theorem exists_familyWedge_homeomorph {J : Type*} {D S : J → Type*}
    [∀ i, TopologicalSpace (D i)] [∀ i, TopologicalSpace (S i)]
    (b : ∀ i, S i) (g : ∀ i, D i → S i)
    (hquot : ∀ i, IsQuotientMap (Sum.elim (fun _ : Unit => b i) (g i)))
    (hker : ∀ i x y, g i x = g i y ↔ x = y ∨ (g i x = b i ∧ g i y = b i)) :
    let C : Set (Unit ⊕ Σ i, D i) :=
      {z | Sum.elim (fun _ => True) (fun a => g a.1 a.2 = b a.1) z}
    ∃ e : Collapse C ≃ₜ CompactWedgeFiniteFactor.FamilyWedge b,
      e (collapseMap C (Sum.inl ())) = CompactWedgeFiniteFactor.base b ∧
      ∀ i x, e (collapseMap C (Sum.inr ⟨i, x⟩)) =
        CompactWedgeFiniteFactor.point b i (g i x) := by
  classical
  dsimp only
  let C : Set (Unit ⊕ Σ i, D i) :=
    {z | Sum.elim (fun _ => True) (fun a => g a.1 a.2 = b a.1) z}
  let bset := CompactWedgeFiniteFactor.basePoints b
  let raw : (Unit ⊕ Σ i, D i) → (Unit ⊕ Σ i, S i) :=
    Sum.map id (fun a => ⟨a.1, g a.1 a.2⟩)
  let map : C(Unit ⊕ Σ i, D i, CompactWedgeFiniteFactor.FamilyWedge b) :=
    ⟨collapseMap bset ∘ raw, (collapseMap bset).continuous.comp
      (continuous_id.sumMap (continuous_sigma (fun i => continuous_sigmaMk.comp
        ((hquot i).continuous.comp continuous_inr))))⟩
  have hbase (z : Unit ⊕ Σ i, D i) : raw z ∈ bset ↔ z ∈ C := by
    rcases z with _ | ⟨i, x⟩
    · exact iff_of_true (Or.inl (congrArg Sum.inl (Subsingleton.elim _ ()))) trivial
    · change ((Sum.inr (⟨i, g i x⟩ : Sigma S) : Unit ⊕ Sigma S) = Sum.inl () ∨
          ∃ j, Sum.inr (⟨i, g i x⟩ : Sigma S) = Sum.inr ⟨j, b j⟩) ↔ g i x = b i
      constructor
      · rintro (h | ⟨j, h⟩)
        · cases h
        · have hi : i = j := congrArg Sigma.fst (Sum.inr.inj h)
          subst j
          exact sigma_mk_injective (Sum.inr.inj h)
      · intro hx
        exact Or.inr ⟨i, by rw [hx]⟩
  have hmapq : IsQuotientMap map := by
    refine ⟨IsCoinducing.of_isOpen_preimage_iff_isOpen ?_, ?_⟩
    · intro U
      constructor
      · intro hU
        apply isQuotientMap_quotient_mk'.isCoinducing.isOpen_preimage.mp
        refine isOpen_sum_iff.mpr ⟨?_, isOpen_sigma_iff.mpr ?_⟩
        · have hu := isOpen_sum_iff.mp hU |>.1
          exact hu
        · intro i
          change IsOpen (CompactWedgeFiniteFactor.point b i ⁻¹' U)
          apply (hquot i).isCoinducing.isOpen_preimage.mp
          refine isOpen_sum_iff.mpr ⟨?_, ?_⟩
          · exact isOpen_discrete _
          · have hi := isOpen_sigma_iff.mp (isOpen_sum_iff.mp hU).2 i
            exact hi
      · intro hU
        exact hU.preimage map.continuous
    · intro u
      refine Quotient.inductionOn u ?_
      intro z
      rcases z with _ | ⟨i, y⟩
      · exact ⟨Sum.inl (), congrArg (fun a => collapseMap bset (Sum.inl a))
          (Subsingleton.elim _ _)⟩
      · obtain ⟨z, hz⟩ := (hquot i).surjective y
        rcases z with _ | x
        · change b i = y at hz
          exact ⟨Sum.inl (), (CompactWedgeFiniteFactor.point_base b i).symm.trans
            (congrArg (CompactWedgeFiniteFactor.point b i) hz)⟩
        · exact ⟨Sum.inr ⟨i, x⟩, congrArg (CompactWedgeFiniteFactor.point b i) hz⟩
  have hmapKer (z w : Unit ⊕ Σ i, D i) :
      (subsetSetoid C).r z w ↔ map z = map w := by
    change (z = w ∨ (z ∈ C ∧ w ∈ C)) ↔
      collapseMap bset (raw z) = collapseMap bset (raw w)
    rw [show collapseMap bset (raw z) = collapseMap bset (raw w) ↔
      raw z = raw w ∨ (raw z ∈ bset ∧ raw w ∈ bset) from Quotient.eq, hbase, hbase]
    refine ⟨?_, ?_⟩
    · rintro (rfl | h)
      · exact Or.inl rfl
      · exact Or.inr h
    · rintro (he | h)
      · rcases z with z | ⟨i, x⟩ <;> rcases w with w | ⟨j, y⟩
        · exact Or.inl (congrArg Sum.inl (Subsingleton.elim z w))
        · cases he
        · cases he
        · change Sum.inr (⟨i, g i x⟩ : Sigma S) = Sum.inr ⟨j, g j y⟩ at he
          have hij : i = j := congrArg Sigma.fst (Sum.inr.inj he)
          subst j
          rcases (hker i x y).mp (sigma_mk_injective (Sum.inr.inj he)) with rfl | hb
          · exact Or.inl rfl
          · exact Or.inr hb
      · exact Or.inr h
  let e := (Homeomorph.Quotient.congrRight hmapKer).trans
    (Topology.IsQuotientMap.homeomorph (f := map) hmapq)
  exact ⟨e, rfl, fun _ _ => rfl⟩

open D5.S3.Geometry.EuclideanSphereJoin (StdSphere)
open D5.S3.Geometry.FiniteSimplexBoundarySphere
open D5.S3.Geometry.FiniteAttachmentQuotient
open D5.S3.TotalVariation.FairBiasShelling

private def diskCoordinates (c : L → A) (B : fullRestrictionFacets c) :
    Space (simplexOn B.val) ≃ₜ Simplex (FaceIndex (L × Bool) B.val) := by
  have hne := ((signedComplex c).isRelLowerSet_faces (mem_facets.mp B.property.1).1).1
  exact (Homeomorph.setCongr (simplexOn_realization B.val hne)).trans
    (faceCoordinateHomeomorph B.val).symm

private theorem diskCoordinates_boundary (c : L → A) (B : fullRestrictionFacets c)
    (x : Space (simplexOn B.val)) :
    boundary (diskCoordinates c B x) ↔ diskIn c B x ∈ coreSet c := by
  rw [diskIn_mem_core_iff_boundary]
  have he := faceCoordinateHomeomorph_boundary B.val (diskCoordinates c B x)
  rw [show faceCoordinateHomeomorph B.val (diskCoordinates c B x) =
      (Homeomorph.setCongr (simplexOn_realization B.val
        (((signedComplex c).isRelLowerSet_faces (mem_facets.mp B.property.1).1).1))) x from
    (faceCoordinateHomeomorph B.val).apply_symm_apply _] at he
  simpa [faceBoundary, Homeomorph.setCongr] using he.symm

private def wedgeDimension (c : L → A) : ℕ :=
  Fintype.card L - Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range c)) - 1

private theorem exists_disk_sphere_map (c : L → A) (B : fullRestrictionFacets c) :
    ∃ b : StdSphere (wedgeDimension c),
      ∃ g : Space (simplexOn B.val) → StdSphere (wedgeDimension c),
      IsQuotientMap (Sum.elim (fun _ : Unit => b) g) ∧
      (∀ x, g x = b ↔ diskIn c B x ∈ coreSet c) ∧
      (∀ x y, g x = g y ↔ x = y ∨ (g x = b ∧ g y = b)) := by
  classical
  let _ : DecidableEq (L × Bool) := LinearOrder.toDecidableEq
  let D := Space (simplexOn B.val)
  let Λ := FaceIndex (L × Bool) B.val
  let e := diskCoordinates c B
  have hn := ((signedComplex c).isRelLowerSet_faces (mem_facets.mp B.property.1).1).1
  let _ : Nonempty Λ := ⟨⟨hn.choose, hn.choose_spec⟩⟩
  let _ : CompactSpace D := D5.S3.Geometry.FiniteSimplicialJoin.realizationCompactSpace
    (simplexOn B.val)
  have hcard : Fintype.card Λ = B.val.card := Fintype.card_coe B.val
  have hdim : Fintype.card Λ - 1 = wedgeDimension c := by
    rw [hcard, facet_card_eq_nullity c B.val (mem_facets.mp B.property.1)]
    rfl
  let transport : StdSphere (Fintype.card Λ - 1) ≃ₜ StdSphere (wedgeDimension c) := hdim ▸
    Homeomorph.refl _
  by_cases hm : 2 ≤ Fintype.card Λ
  · let s := (reindexSphere (stdIndex hm)).trans transport
    let b := s south
    let g : D → StdSphere (wedgeDimension c) := fun x => s (psi (e x))
    have hb (x : D) : g x = b ↔ diskIn c B x ∈ coreSet c :=
      s.injective.eq_iff.trans ((psi_south_iff _).trans (diskCoordinates_boundary c B x))
    refine ⟨b, g, IsQuotientMap.of_surjective_continuous ?_ ?_, hb, ?_⟩
    · intro y
      obtain ⟨x, hx⟩ := psi_surjective hm (s.symm y)
      refine ⟨Sum.inr (e.symm x), ?_⟩
      change s (psi (e (e.symm x))) = y
      rw [e.apply_symm_apply, hx, s.apply_symm_apply]
    · exact continuous_const.sumElim (s.continuous.comp
        ((continuous_psiRaw.subtype_mk fun x => (psi x).property).comp e.continuous))
    · intro x y
      change s (psi (e x)) = s (psi (e y)) ↔ _
      rw [s.injective.eq_iff, psi_eq_iff]
      change (e x = e y ∨ (boundary (e x) ∧ boundary (e y))) ↔ _
      rw [e.injective.eq_iff, diskCoordinates_boundary, diskCoordinates_boundary, hb, hb]
  · have hone : Fintype.card Λ = 1 :=
      le_antisymm (by omega) (Fintype.card_pos)
    let _ : Subsingleton Λ := Fintype.card_le_one_iff_subsingleton.mp hone.le
    let i : Λ := Classical.choice inferInstance
    have hcoordinates (x : Simplex Λ) (j : Λ) : x.val j = 1 := by
      have hu : (Finset.univ : Finset Λ) = {j} := by
        ext k
        simp [Subsingleton.elim k j]
      simpa [hu] using x.property.2
    have hsingle (x y : D) : x = y := by
      apply e.injective
      apply Subtype.ext
      apply PiLp.ext
      intro j
      exact (hcoordinates (e x) j).trans (hcoordinates (e y) j).symm
    have hnone (x : D) : diskIn c B x ∉ coreSet c := by
      intro hx
      obtain ⟨j, hz⟩ := (diskCoordinates_boundary c B x).mpr hx
      exact one_ne_zero ((hcoordinates (e x) j).symm.trans hz)
    let Hd : StdSphere 0 ≃ₜ StdSphere (wedgeDimension c) :=
      (by omega : 0 = wedgeDimension c) ▸ Homeomorph.refl _
    let s := ((boolTwoPointHomeomorph).trans twoPointSphereHomeomorph).trans Hd
    let b := s false
    let g : D → StdSphere (wedgeDimension c) := fun _ => s true
    refine ⟨b, g, IsQuotientMap.of_surjective_continuous ?_
      (continuous_const.sumElim continuous_const), ?_, ?_⟩
    · intro y
      obtain ⟨k, rfl⟩ := s.surjective y
      cases k
      · exact ⟨Sum.inl (), rfl⟩
      · exact ⟨Sum.inr (e.symm (vertex i)), rfl⟩
    · intro x
      exact ⟨fun he => (Bool.noConfusion (s.injective he)), fun hx => (hnone x hx).elim⟩
    · intro x y
      exact ⟨fun _ => Or.inl (hsingle x y), fun _ => rfl⟩

/-- The canonical core projection is a homotopy equivalence. Its target is the ordinary
wedge of one standard sphere per full-restriction facet, with the core class as basepoint. -/
theorem exists_spherical_wedge (c : L → A) (h : (facets c).Nonempty) :
    let d := Fintype.card L - Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range c)) - 1
    ∃ b : fullRestrictionFacets c → StdSphere d,
      ∃ g : ∀ B : fullRestrictionFacets c, Space (simplexOn B.val) → StdSphere d,
        ∃ e : Collapse (coreSet c) ≃ₜ CompactWedgeFiniteFactor.FamilyWedge b,
          ∃ p : coreSet c, ∃ H : Space (signedComplex c) ≃ₕ Collapse (coreSet c),
            e (collapseMap (coreSet c) p) = CompactWedgeFiniteFactor.base b ∧
            H.toFun = collapseMap (coreSet c) ∧
            ∀ B, Function.Surjective (Sum.elim (fun _ : Unit => b B) (g B)) ∧
              ∀ x, e (collapseMap (coreSet c) (diskIn c B x)) =
                CompactWedgeFiniteFactor.point b B (g B x) := by
  classical
  let _ : DecidableEq (L × Bool) := LinearOrder.toDecidableEq
  dsimp only
  choose b g hquot hb hker using exists_disk_sphere_map c
  obtain ⟨eFamily, heFamily, heDisk⟩ := exists_familyWedge_homeomorph b g hquot hker
  obtain ⟨p, eAttach, hp, hDisk⟩ := exists_core_attachment_homeomorph c h
  have hAttach :
      attachingSet (diskIn c) (coreSet c) =
        {z | Sum.elim (fun _ => True) (fun a => g a.1 a.2 = b a.1) z} := by
    ext z
    rcases z with _ | ⟨i, x⟩
    · rfl
    · exact (hb i x).symm
  let eChange := Homeomorph.Quotient.congrRight
    (r := subsetSetoid (attachingSet (diskIn c) (coreSet c)))
    (r' := subsetSetoid
      {z | Sum.elim (fun _ => True) (fun a => g a.1 a.2 = b a.1) z})
    (fun x y => by rw [hAttach])
  obtain ⟨H, hH⟩ := exists_core_collapse_equiv c h
  refine ⟨b, g, (eAttach.symm.trans eChange).trans eFamily, p, H, ?_, hH, ?_⟩
  · change eFamily (eChange (eAttach.symm (collapseMap (coreSet c) p))) = _
    rw [← hp, eAttach.symm_apply_apply]
    exact heFamily
  · intro B
    refine ⟨(hquot B).surjective, ?_⟩
    intro x
    change eFamily (eChange (eAttach.symm (collapseMap (coreSet c) (diskIn c B x)))) = _
    rw [← hDisk B x, eAttach.symm_apply_apply]
    exact heDisk B x

#print axioms exists_spherical_wedge

end D5.S3.TotalVariation.FairBiasSphericalWedge
