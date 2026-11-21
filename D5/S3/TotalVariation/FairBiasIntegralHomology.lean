/- GID: D5/S3/TotalVariation/FairBiasIntegralHomology
   generality: G
   mirror-B: D5/B/S3/TotalVariation/FairBiasIntegralHomology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reduced integral homology of the actual signed fair-bias realization. -/
import D5.S3.Topology.PointedWedgeHomology
import D5.S3.Geometry.FiniteFamilyWedgeSplit
import D5.S3.Geometry.EuclideanSphereJoin
import D5.S3.Topology.SphereHomologyAllDegrees
import D5.S3.Topology.TauCeti.AlgebraicTopology.Sphere.Puncture
import Batteries.Tactic.OpenPrivate
import D5.S3.Geometry.CompactWedgeFiniteFactor
import D5.S3.Geometry.FiniteComponentClosure.BasedJoin
import Mathlib.Analysis.Normed.Module.Connected
import D5.S3.TotalVariation.FairBiasSphericalWedge
import D5.S3.Topology.TauCeti.AlgebraicTopology.Singular.Reduced
open Set Topology Metric ContinuousMap NormedSpace Module
open scoped unitInterval
open D5.S3.Geometry.FiniteConeUnionWedge
open D5.S3.Geometry.CompactWedgeFiniteFactor
open D5.S3.Geometry.FiniteFamilyWedgeSplit
open D5.S3.Topology.PointedWedgeHomology
open D5.S3.Geometry.FiniteComponentClosure
open D5.S3.Geometry.EuclideanSphereJoin

namespace D5.S3.TotalVariation.FairBiasIntegralHomology
noncomputable section

private def OpenBasedContraction {X : Type*} [TopologicalSpace X] (a : X) : Prop :=
  ∃ (A : Set X) (_ : IsOpen A) (ha : a ∈ A),
    Nonempty ((ContinuousMap.id A).HomotopyRel (ContinuousMap.const A ⟨a, ha⟩) {⟨a, ha⟩})

private def transportContraction {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (a : X) (h : (ContinuousMap.id X).HomotopyRel (ContinuousMap.const X a) {a}) :
    (ContinuousMap.id Y).HomotopyRel (ContinuousMap.const Y (e a)) {e a} where
  toFun z := e (h (z.1, e.symm z.2))
  continuous_toFun := e.continuous.comp
    (h.continuous.comp (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))
  map_zero_left y := by rw [h.apply_zero]; exact e.apply_symm_apply y
  map_one_left y := by rw [h.apply_one]; rfl
  prop' t y hy := by
    rw [mem_singleton_iff] at hy
    subst y
    change e (h (t, e.symm (e a))) = e a
    rw [e.symm_apply_apply, h.eq_fst t (mem_singleton a)]
    rfl

private theorem openBasedContraction_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {a : X} (h : OpenBasedContraction a) : OpenBasedContraction (e a) := by
  obtain ⟨A, hA, ha, ⟨H⟩⟩ := h
  refine ⟨e.symm ⁻¹' A, hA.preimage e.symm.continuous, ?_, ?_⟩
  · change e.symm (e a) ∈ A
    rwa [e.symm_apply_apply]
  · let E : A ≃ₜ (e.symm ⁻¹' A) := (e.symm.sets rfl).symm
    have he : E ⟨a, ha⟩ = ⟨e a, by simpa⟩ := Subtype.ext rfl
    exact ⟨by simpa only [he] using transportContraction E ⟨a, ha⟩ H⟩

open private wedgeInverseHomotopy wedgeMap from D5.S3.Geometry.FiniteConeUnionWedge

private def wedgeContraction {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {a : X} {b : Y}
    (H : (ContinuousMap.id X).HomotopyRel (ContinuousMap.const X a) {a})
    (K : (ContinuousMap.id Y).HomotopyRel (ContinuousMap.const Y b) {b}) :
    (ContinuousMap.id (Wedge a b)).HomotopyRel
      (ContinuousMap.const _ (Quotient.mk _ (Sum.inl a))) {Quotient.mk _ (Sum.inl a)} := by
  let c := Quotient.mk (subsetSetoid (wedgePoints a b)) (Sum.inl a)
  have Hr : (ContinuousMap.id X).HomotopyRel ((ContinuousMap.const X a).comp
      (ContinuousMap.id X)) {a} := H.cast rfl (by ext; rfl)
  have Kr : (ContinuousMap.id Y).HomotopyRel ((ContinuousMap.const Y b).comp
      (ContinuousMap.id Y)) {b} := K.cast rfl (by ext; rfl)
  let F := wedgeInverseHomotopy (ContinuousMap.id X) (ContinuousMap.id Y)
      (ContinuousMap.const X a) (ContinuousMap.const Y b) rfl rfl rfl rfl Hr Kr
  have hend : (wedgeMap (a := a) (b := b) (a' := a) (b' := b)
      (ContinuousMap.const X a) (ContinuousMap.const Y b) rfl rfl).comp
      (wedgeMap (a := a) (b := b) (a' := a) (b' := b)
        (ContinuousMap.id X) (ContinuousMap.id Y) rfl rfl) =
      ContinuousMap.const _ c := by
    apply ContinuousMap.ext
    intro z
    refine Quotient.inductionOn z ?_
    rintro (x | y)
    · rfl
    · exact Quotient.sound (Or.inr ⟨Or.inr rfl, Or.inl rfl⟩)
  refine { toHomotopy := F.cast rfl hend, prop' := ?_ }
  intro t z hz
  have hz' : z = c := hz
  subst z
  change Quotient.mk (subsetSetoid (wedgePoints a b)) (Sum.inl (Hr (t, a))) = c
  rw [Hr.eq_fst t (mem_singleton a)]
  rfl

universe top
private theorem openBasedContraction_wedge {X Y : Type top} [TopologicalSpace X] [TopologicalSpace Y]
    {a : X} {b : Y} (h : OpenBasedContraction a) (k : OpenBasedContraction b) :
    OpenBasedContraction (Quotient.mk (subsetSetoid (wedgePoints a b)) (Sum.inl a)) := by
  obtain ⟨A, hA, ha, ⟨H⟩⟩ := h
  obtain ⟨B, hB, hb, ⟨K⟩⟩ := k
  have hc : Quotient.mk (subsetSetoid (wedgePoints a b)) (Sum.inl a) ∈ part a b A B ha hb := ha
  refine ⟨part a b A B ha hb, isOpen_part a b hA hB ha hb, hc, ?_⟩
  let e := partHomeomorph a b hA hB ha hb
  exact ⟨transportContraction e (Quotient.mk _ (Sum.inl ⟨a, ha⟩)) (wedgeContraction H K)⟩

open private
  smul_sub_smul_ne_zero_of_ne normalize_smul_sub_smul_ne_of_ne normalizeSegmentToSphere
  coe_normalizeSegmentToSphere_apply coe_normalizeSegmentToSphere_zero_left
  coe_normalizeSegmentToSphere_one_left coe_normalizeSegmentToSphere_apply_of_eq
  from D5.S3.Topology.TauCeti.AlgebraicTopology.Sphere.Puncture

private theorem sphereOpenBasedContraction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : sphere (0 : E) 1) : OpenBasedContraction b := by
  let p := -b
  have hp : ‖(p : E)‖ = 1 := mem_sphere_zero_iff_norm.mp p.property
  have hbp : b ≠ p := ne_neg_of_mem_unit_sphere ℝ b
  let A : Set (sphere (0 : E) 1) := {p}ᶜ
  let a : A := ⟨b, hbp⟩
  have hcenter : -(p : E) = (b : E) := by simp [p]
  let inclusion (q : A) : E := q.val.val
  have hsegment : ∀ z : I × A,
      (1 - (z.1 : ℝ)) • inclusion z.2 + (z.1 : ℝ) • (-(p : E)) ≠ 0 := by
    rintro ⟨u, q⟩
    simpa only [inclusion, smul_neg, sub_eq_add_neg] using smul_sub_smul_ne_zero_of_ne
      (mem_sphere_zero_iff_norm.mp q.val.property) hp
      (fun hq => q.property (Set.mem_singleton_iff.mpr (Subtype.ext hq))) u
  let G := normalizeSegmentToSphere inclusion (fun _ => -(p : E))
    (continuous_subtype_val.comp continuous_subtype_val) continuous_const hsegment
  have hGne (z : I × A) : G z ∈ A := by
    rcases z with ⟨u, q⟩
    change G (u, q) ≠ p
    intro he
    apply normalize_smul_sub_smul_ne_of_ne (mem_sphere_zero_iff_norm.mp q.val.property) hp
      (fun hq => q.property (Set.mem_singleton_iff.mpr (Subtype.ext hq))) u
    have hval := congrArg Subtype.val he
    simpa only [G, coe_normalizeSegmentToSphere_apply, inclusion, smul_neg,
      ← sub_eq_add_neg] using hval
  refine ⟨A, isClosed_singleton.isOpen_compl, a.property, ⟨?_⟩⟩
  refine {
    toFun := fun z => ⟨G z, hGne z⟩
    continuous_toFun := G.continuous.subtype_mk hGne
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }
  · intro q
    apply Subtype.ext ∘ Subtype.ext
    change ((G (0, q)).val : E) = inclusion q
    rw [coe_normalizeSegmentToSphere_zero_left]
    exact normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp q.val.property)
  · intro q
    apply Subtype.ext ∘ Subtype.ext
    change ((G (1, q)).val : E) = (b : E)
    rw [coe_normalizeSegmentToSphere_one_left, hcenter]
    exact normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp b.property)
  · intro t q hq
    have he : q = a := hq
    subst q
    apply Subtype.ext ∘ Subtype.ext
    exact coe_normalizeSegmentToSphere_apply_of_eq
      (show inclusion a = (b : E) from rfl) hcenter
      (mem_sphere_zero_iff_norm.mp b.property) t

section PositiveHomology

open CategoryTheory Limits AlgebraicTopology

universe u v w
variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

private def splitCoproduct {J : Type w} (M : J → C) (i : J) :
    (∐ M) ≅ M i ⊞ (∐ fun j : {j // j ≠ i} => M j.val) := by
  classical
  let R := fun j : {j // j ≠ i} => M j.val
  let into (j : J) : M j ⟶ M i ⊞ (∐ R) :=
    if h : j = i then eqToHom (congrArg M h) ≫ biprod.inl
    else Sigma.ι R ⟨j, h⟩ ≫ biprod.inr
  refine {
    hom := Sigma.desc into
    inv := biprod.desc (Sigma.ι M i) (Sigma.desc fun j : {j // j ≠ i} => Sigma.ι M j.val)
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  · apply Sigma.hom_ext
    intro j
    by_cases hj : j = i
    · subst j
      simp [into]
    · simp [into, hj, R]
  · apply biprod.hom_ext'
    · simp [into]
      rfl
    · apply Sigma.hom_ext
      intro j
      simp [into, j.property, R]

private theorem subsingletonEmptyWedge {J : Type*} {Z : J → Type*}
    [∀ j, TopologicalSpace (Z j)] [IsEmpty J] (b : ∀ j, Z j) :
    Subsingleton (FamilyWedge b) := by
  have h (x : FamilyWedge b) : x = base b := by
    refine Quotient.inductionOn x ?_
    rintro (u | ⟨j, _⟩)
    · cases u
      rfl
    · exact False.elim (IsEmpty.false j)
  exact ⟨fun x y => (h x).trans (h y).symm⟩

private theorem emptyWedgeContraction {J : Type*} {Z : J → Type*}
    [∀ j, TopologicalSpace (Z j)] [IsEmpty J] (b : ∀ j, Z j) :
    OpenBasedContraction (base b) := by
  let _ := subsingletonEmptyWedge b
  refine ⟨Set.univ, isOpen_univ, mem_univ _, ⟨?_⟩⟩
  exact (ContinuousMap.HomotopyRel.refl _ _).cast rfl
    (by ext; exact Subsingleton.elim _ _)

private theorem cardinalComplement {J : Type w} [Fintype J] (i : J) :
    Nat.card {j : J // j ≠ i} + 1 = Nat.card J := by
  classical
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (· = i)]
  have hcard : Fintype.card {j : J // j = i} = 1 :=
    Fintype.card_unique
  rw [hcard]
  have hJ := Fintype.card_pos_iff.mpr ⟨i⟩
  omega

private theorem finiteFamilyPositiveHomology (R : C) (degree : ℕ) (hd : 0 < degree) :
    ∀ (n : ℕ) {J : Type w} [Fintype J] {Z : J → Type w} [∀ j, TopologicalSpace (Z j)]
      (b : ∀ j, Z j), Nat.card J = n → (∀ j, OpenBasedContraction (b j)) →
      OpenBasedContraction (base b) ∧ Nonempty (
        (∐ fun j => ((singularHomologyFunctor C degree).obj R).obj (TopCat.of (Z j))) ≅
          ((singularHomologyFunctor C degree).obj R).obj (TopCat.of (FamilyWedge b))) := by
  let F : TopCat.{w} ⥤ C := (singularHomologyFunctor C degree).obj R
  intro n
  induction n with
  | zero =>
      intro J _ Z _ b hJ _
      let _ : IsEmpty J := Fintype.card_eq_zero_iff.mp (by simpa using hJ)
      let _ : Subsingleton (FamilyWedge b) := subsingletonEmptyWedge b
      let _ : Nonempty (FamilyWedge b) := ⟨base b⟩
      have hs : IsZero (∐ fun j => F.obj (TopCat.of (Z j))) :=
        (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ (fun j => isEmptyElim j))
      have ht : IsZero (F.obj (TopCat.of (FamilyWedge b))) := by
        exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C degree R _ hd.ne'
      exact ⟨emptyWedgeContraction b, ⟨hs.iso ht⟩⟩
  | succ n ih =>
      intro J _ Z _ b hJ hB
      classical
      have hn : 0 < Fintype.card J := by
        simp only [← Nat.card_eq_fintype_card, hJ, Nat.succ_pos]
      let i : J := Classical.choice (Fintype.card_pos_iff.mp hn)
      let r := fun j : {j // j ≠ i} => b j.val
      have hr : Nat.card {j : J // j ≠ i} = n := by
        have hh := cardinalComplement i
        omega
      obtain ⟨hN, ⟨eN⟩⟩ := ih r hr (fun j => hB j.val)
      let e := (split b i).val
      have he : e (base b) = Quotient.mk _ (Sum.inl (b i)) := (split b i).property.1
      have hW : OpenBasedContraction (Quotient.mk
          (subsetSetoid (wedgePoints (b i) (base r))) (Sum.inl (b i))) :=
        openBasedContraction_wedge (hB i) hN
      have hBase : OpenBasedContraction (base b) := by
        have h := openBasedContraction_homeomorph e.symm hW
        rw [← he, e.symm_apply_apply] at h
        exact h
      refine ⟨hBase, ?_⟩
      obtain ⟨A, hA, ha, ⟨H⟩⟩ := hB i
      obtain ⟨B, hB', hb, ⟨K⟩⟩ := hN
      let eW := D5.S3.Topology.PointedWedgeHomology.homologyIso (b i) (base r) hA hB' ha hb H K R degree hd
      let eF := F.mapIso (TopCat.isoOfHomeo (X := TopCat.of (FamilyWedge b))
        (Y := TopCat.of (Wedge (b i) (base r))) e)
      exact ⟨splitCoproduct (fun j => F.obj (TopCat.of (Z j))) i ≪≫
        biprod.mapIso (Iso.refl _) eN ≪≫ eW ≪≫ eF.symm⟩

end PositiveHomology

section SphereFamilyGroups
open CategoryTheory Limits AlgebraicTopology
open D5.S3.Geometry.EuclideanSphereJoin (StdSphere)

universe u v w
variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
variable {J : Type w} [Fintype J]

private def familyCongr {J : Type*} {Z Y : J → Type*}
    [∀ j, TopologicalSpace (Z j)] [∀ j, TopologicalSpace (Y j)]
    (b : ∀ j, Z j) (e : ∀ j, Z j ≃ₜ Y j) :
    FamilyWedge b ≃ₜ FamilyWedge (fun j => e j (b j)) := by
  let g : Sigma Z ≃ₜ Sigma Y := (IsHomeomorph.sigmaMap Function.bijective_id
    (fun j => (e j).isHomeomorph)).homeomorph
  let h := (Homeomorph.refl Unit).sumCongr g
  apply Homeomorph.Quotient.congr h
  have hm (z : Unit ⊕ Sigma Z) : h z ∈ basePoints (fun j => e j (b j)) ↔
      z ∈ basePoints b := by
    rcases z with u | ⟨j, x⟩
    · cases u
      exact iff_of_true (Or.inl rfl) (Or.inl rfl)
    · change (Sum.inr (⟨j, e j x⟩ : Sigma Y) : Unit ⊕ Sigma Y) ∈
        basePoints (fun j => e j (b j)) ↔ (Sum.inr (⟨j, x⟩ : Sigma Z) : Unit ⊕ Sigma Z) ∈ basePoints b
      constructor
      · rintro (he | ⟨k, hk⟩)
        · cases he
        · have hj : j = k := congrArg Sigma.fst (Sum.inr.inj hk)
          subst k
          have hx : x = b j := (e j).injective (sigma_mk_injective (Sum.inr.inj hk))
          exact Or.inr ⟨j, by rw [hx]⟩
      · rintro (he | ⟨k, hk⟩)
        · cases he
        · have hj : j = k := congrArg Sigma.fst (Sum.inr.inj hk)
          subst k
          have hx : x = b j := sigma_mk_injective (Sum.inr.inj hk)
          exact Or.inr ⟨j, by rw [hx]⟩
  intro x y
  change (x = y ∨ (x ∈ _ ∧ y ∈ _)) ↔
    (h x = h y ∨ (h x ∈ _ ∧ h y ∈ _))
  rw [h.injective.eq_iff, hm, hm]

private theorem positiveWedgeGroups (R : C) (d k : ℕ) (b : J → StdSphere d) :
    let H := TauCeti.reducedSingularHomologyFunctor R (k + 1)
    (d = k + 1 → Nonempty (H.obj (TopCat.of (FamilyWedge b)) ≅ ∐ fun _ : J => R)) ∧
    (d ≠ k + 1 → IsZero (H.obj (TopCat.of (FamilyWedge b)))) := by
  let E := EuclideanSpace ℝ (ULift.{w} (Fin (d + 1)))
  let Iₑ : EuclideanSpace ℝ (Fin (d + 1)) ≃ₗᵢ[ℝ] E :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ Equiv.ulift.symm
  let c : StdSphere d ≃ₜ sphere (0 : E) 1 := Iₑ.toHomeomorph.subtype (fun x => by
    rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm]
    change ‖x‖ = 1 ↔ ‖Iₑ x‖ = 1
    rw [Iₑ.norm_map])
  let h : J → sphere (0 : E) 1 := fun j => c (b j)
  let W := familyCongr b (fun _ => c)
  let H := TauCeti.reducedSingularHomologyFunctor R (k + 1)
  let S : J → C := fun _ => H.obj (TopCat.of (sphere (0 : E) 1))
  let basis : OrthonormalBasis (Fin (d + 1)) ℝ E :=
    (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).map Iₑ
  let e := (finiteFamilyPositiveHomology R (k + 1) (Nat.succ_pos k) (Nat.card J) h rfl
    (fun j => sphereOpenBasedContraction (h j))).2.some
  let es : (∐ S) ≅ H.obj (TopCat.of (FamilyWedge h)) :=
    Sigma.whiskerEquiv (Equiv.refl J)
        (fun _ => (TauCeti.reducedSingularHomologySuccIso R k).app
          (TopCat.of (sphere (0 : E) 1))) ≪≫
      e ≪≫ ((TauCeti.reducedSingularHomologySuccIso R k).app _).symm
  let ew := W.toHomotopyEquiv.reducedSingularHomologyIso R (k + 1)
  constructor
  · intro hdim
    have hS (j : J) : S j ≅ R := by
      dsimp only [S, H]
      subst d
      exact TauCeti.reducedSingularHomologySphereIso R basis
    exact ⟨ew ≪≫ es.symm ≪≫ Sigma.whiskerEquiv (Equiv.refl J) (fun j => (hS j).symm)⟩
  · intro hdim
    have hZ (j : J) : IsZero (S j) :=
      D5.S3.Topology.SphereHomologyAllDegrees.isZero_reducedHomology_sphere
        R basis (k + 1) hdim.symm
    have hz : IsZero (∐ S) := by
      apply (IsZero.iff_id_eq_zero _).2
      apply Sigma.hom_ext
      intro j
      exact (hZ j).eq_of_src _ _
    exact hz.of_iso (ew ≪≫ es.symm)

end SphereFamilyGroups

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

private theorem fairBiasZeroAndNullityOne (c : L → A) (h : (facets c).Nonempty) :
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

/-- Reduced integral singular homology of the actual signed realization. -/
theorem reducedHomology_eq_fullRestrictionFacets (c : L → A) (h : (facets c).Nonempty) (k : ℕ) :
    let d := Fintype.card L - Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range c)) - 1
    let R := ModuleCat.of ℤ (ULift.{v} ℤ)
    let X := TopCat.of (Space (signedComplex c))
    let H := (TauCeti.reducedSingularHomologyFunctor R k).obj X
    (k = d → Nonempty (H ≅ ∐ fun _ : fullRestrictionFacets c => R)) ∧
      (k ≠ d → IsZero H) := by
  let d := Fintype.card L - Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range c)) - 1
  let R := ModuleCat.of ℤ (ULift.{v} ℤ)
  cases k with
  | zero =>
      obtain ⟨zeroDim, positiveDim⟩ := fairBiasZeroAndNullityOne c h
      exact ⟨fun h => (zeroDim h.symm).1, fun h => positiveDim (Nat.pos_of_ne_zero (Ne.symm h))⟩
  | succ k =>
      let _ : Fintype (fullRestrictionFacets c) := Fintype.ofFinite _
      obtain ⟨b, _, e, _, H, _, _, _⟩ := exists_spherical_wedge c h
      let iso := (H.trans e.toHomotopyEquiv).reducedSingularHomologyIso R (k + 1)
      obtain ⟨equal, different⟩ := positiveWedgeGroups R d k b
      exact ⟨fun h => ⟨iso ≪≫ (equal h.symm).some⟩,
        fun h => (different (Ne.symm h)).of_iso iso⟩

#print axioms reducedHomology_eq_fullRestrictionFacets

end FairBias
end
end D5.S3.TotalVariation.FairBiasIntegralHomology
