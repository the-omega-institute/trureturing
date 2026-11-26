/- GID: D5/S3/Zeros/GRH/Lib/Shimura/AbelianScheme/Specialisation
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/AbelianScheme/Specialisation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.AbelianScheme.Specialisation. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/AbelianScheme/Specialisation.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Geometry.SeparatingPoints
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of algebraic geometry (textbook or folklore).

Part of: Abelian schemes: isogenies finite flat, [m]*L = L^{m²}, Cartier, unramified torsion (known
result; see Lib.Shimura.AbelianScheme.ThetaFamily).

This file: Geometric points in locally closed sets; homogeneity and dimension of group schemes.
Properties at geometric specialisations; flat maps are injective on stalks. -/

open CategoryTheory AlgebraicGeometry MonoidalCategory Scheme Over Limits.pullback Pullback Set
variable {k X} [Field k] [IsAlgClosed k] (s : X ⟶ Spec ⟨k⟩) [l : LocallyOfFiniteType s]

/-- For X locally of finite type over an algebraically closed field k, every non-empty locally
closed subset S of X contains a k-rational point. -/
lemma exists_point_mem {S} (hS : IsLocallyClosed S) (h : S.Nonempty) : ∃ x : 𝟙_ _ ⟶ Over.mk s,
  x.left (default : Spec _) ∈ S := (@nonempty_inter_closedPoints X _ l.jacobsonSpace _ h hS).elim
  fun x ⟨_, h⟩ ↦ ⟨homMk _ (pointOfClosedPoint_comp s x h), by simpa [pointOfClosedPoint]⟩

/-- Let f : X → S be locally of finite type and k algebraically closed. A k-point t of S whose
image lies in the image of f lifts to a k-point y of X with f ∘ y = t. -/
lemma exists_point_over {S} (f : X ⟶ S) [LocallyOfFiniteType f] {t : Spec ⟨k⟩ ⟶ S} (e : t
    (IsLocalRing.closedPoint k) ∈ range f) : ∃ y, y ≫ f = t := (exists_point_mem (snd ..)
  isOpen_univ.isLocallyClosed ⟨((range_snd ..).ge e).choose, ⟨⟩⟩).elim fun x _ ↦
  ⟨_ ≫ _, x.w_assoc t ▸ _ ≫= condition⟩

/-- Let f : A → S be smooth and η_i dense complex points of S. If every complex point of A over
some η_i is one of the points ξ_z, then the ξ_z are dense in A. -/
lemma IsDenseFamily.of_fibres {A S κ Z η} (d : @IsDenseFamily κ S η) f [s : @Smooth A S f] {ξ : Z →
  _} (h : ∀ i y, y ≫ f =
  η i → ∃ z, ξ z = y) : IsDenseFamily ξ := (d.preimage f.isOpenMap).induction (fun x ⟨i, e⟩ ↦
  mem_closure_iff.2 fun U u m ↦ (exists_point_over (Opens.ι ⟨U, u⟩ ≫ f) (by tauto)).elim
  fun y e ↦ (h i (y ≫ Opens.ι _) e).elim fun z e ↦ ⟨_, (y _).2, z, congr($e _)⟩) (by simp)

/-- Let X be a commutative group scheme locally of finite type over an algebraically closed
field k, and P a morphism property induced by a property Q of ring maps. If a non-empty open
subscheme has P over k, so does X. -/
lemma AddObj.of_chart {P Q} [HasRingHomProperty P Q] (_ : AddObj (.mk s)) {Y} (i : Y ⟶ X)
    [IsOpenImmersion i] (v : Nonempty Y) (h : P (i ≫ s)) : P s := (exists_point_mem s
  i.isLocallyClosed_range (range_nonempty _)).elim fun y e ↦
  let t z := i ≫ (translation (A := .mk s) z).1
  IsZariskiLocalAtSource.of_openCover (.mkOfCovers _ _ t (by simpa using
    (exists_point_mem s (⨆ z, (t z).opensRange).compl.2.isLocallyClosed).mt (by simpa using (⟨· - y,
     e.imp (by simp_all [← Hom.comp_apply, ← comp_left, t])⟩)))) fun z ↦ i ≫= (translation z).w ▸ h

/-- Let A be an abelian scheme over S with dense complex points y_i over η_i. If g is the only
possible relative dimension of each fibre over η_i, then A is smooth of relative dimension g
over S. -/
lemma AddObj.smoothOfRelativeDimension_of_fibres {S κ g A} [IsAbelianScheme A] {η : κ →
  (Spec ⟨ℂ⟩ ⟶ S)} {y : ∀ i, .mk (η i) ⟶ A} (d : IsDenseFamily (y · |>.left)) (H : ∀ i n,
  SmoothOfRelativeDimension n (snd A.hom (η i)) → n = g) : SmoothOfRelativeDimension g A.hom := ⟨by
  peel Smooth.exists_isStandardSmooth A.hom with x _ u V v m _ h
  obtain ⟨⟨ι, σ, a, b, ⟨P⟩⟩, i, _⟩ := h, d.exists_mem_open V.2 ⟨x, m⟩
  use ι, σ, a, b, P, H i _ ((pullbackAddObj _).of_chart _ (snd v.fromSpec _) ((range_snd ..).ge (by
    simpa [← Hom.comp_apply, lift_fst] : lift _ (𝟙 _) (y i).w _ ∈ _)).nonempty
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).1
    (.paste_vert (.of_hasPullback ..) (.of_hasPullback ..)) (u.SpecMap_appLE_fromSpec .. ▸
    smoothOfRelativeDimension_comp _ 0 (hf := HasRingHomProperty.Spec_iff.2 (RingHom.locally_of
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ (by use! ι, σ, a, b, P, rfl))) ..)))⟩

open RingHom.FaithfullyFlat Flat

/-- For a scheme S and a property Q of field-valued points: every point of S specialises to the
image of some point over an algebraically closed field satisfying Q. -/
def AllSpecializeTo S (Q : ∀ {k} [Field.{0} k], (Spec ⟨k⟩ ⟶ S) → _) := ∀ s, ∃ᵉ (k)
  (_ : Field k) (_ : IsAlgClosed k) (t), s ⤳ t (IsLocalRing.closedPoint k) ∧ Q t

instance {Z} s : Flat (fromSpecStalk Z s) := (SpecMap_iff.2 ((isAffineOpen_opensRange
  _).isLocalization_stalk (id ⟨s, Cover.covers ..⟩)).flat).comp ..

lemma stalkMap_injective_of_flat {X Y} q [@Flat X Y q] y : (⇑(q.stalkMap y)).Injective := injective
  (@.of_flat_of_isLocalHom _ _ _ _ (_) _ _ (stalkMap ..) (q.prop _))
