import OmegaMath.NumberTheory.GRH.Lib.Shimura.Uniformisation.HolomorphicFamily
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic geometry (textbook or folklore).

This file: Very general point of a holomorphic family by Baire; countable residue fields.
Schematically dense complex points determine functions, morphisms and maps to projective space. -/

open CategoryTheory AlgebraicGeometry IsLocalRing PointFn Algebra Spec Limits Set Over LineBundle
  equalizer
variable {P} [FinComplexSpace P] {U : Set P} {X R} (s :
  X ⟶ Spec R) [Countable R] [LocallyOfFiniteType s]
include s

lemma countable_sections {W} (h : IsAffineOpen W) : Countable Γ(X, W) :=
  (HasRingHomProperty.Spec_iff.1 (map_preimage (h.fromSpec ≫ s) ▸ locallyOfFiniteType_comp ..) |>
  (@FiniteType.iff_quotient_mvPolynomial _ _ _ _ (_)).1).choose_spec.choose_spec.comp
  AddMonoidAlgebra.coeffEquiv.3.surjective |>.countable

/-- Let X be locally of finite type over a countable ring R. Every field-valued point t of X
factors through the residue field of some point z of X, and this residue field is countable. -/
lemma exists_countable_residue_point {K} [Field K] t : ∃ᵉ (z) (φ : X.residueField z →+* K), specMap
  φ ≫ X.fromSpecResidueField z = t ∧ Countable (X.residueField z) := ⟨_, _, (X.SpecToEquivOfField
  _).3 t, (exists_isAffineOpen_landsIn t).elim fun _ ⟨W, h⟩ ↦ have := countable_sections s W
  (residue_surjective.comp (W.isLocalization_stalk (id ⟨_, h ⟨⟩⟩)).mk'_surjective).countable⟩

/-- Let X be locally of finite type over a countable ring R. A family φ of complex points of X,
holomorphic on a nonempty connected open U, has a member φ(b), b ∈ U, whose Zariski closure
contains every φ(c), c ∈ U. -/
lemma exists_generic_member {φ : P → (_ ⟶ X)} (u : IsOpen U) (n : IsConnected U) (h : ∀ b ∈ U,
  HolomorphicAt φ b) : ∃ b ∈ U, ∀ c ∈ U,
  φ b (closedPoint ℂ) ⤳ φ c (closedPoint ℂ) := have ⟨c, m⟩ := n.1
  have K {V} hV c (hc : c ∈ closure V ∩ U) : ∃ b ∈ V,
    _ := have ⟨W, hW, h0⟩ := exists_isAffineOpen_landsIn _
    have := countable_sections s hW
    have ⟨N, ⟨o, m, k⟩, H⟩ := (LocallyConnectedSpace.open_connected_basis c).mem_iff.1
      ((u.eventually_mem hc.2).and (h _ hc.2 (isRegularOn_ofSection 0) h0).1)
    have A f : AnalyticOnNhd .. := fun _ w ↦ ((H w).elim (h _ · (isRegularOn_ofSection f))).2
    ((dense_of_mem_residual (eventually_countable_forall.2 fun f ↦ closure_residualEq ((A
      f).continuousOn.isOpen_inter_preimage o isOpen_ne).isLocallyClosed)).exists_mem_open (o.inter
      hV) (by grind [mem_closure_iff])).imp fun b ⟨D, hb, v⟩ ↦ ⟨v, interior_maximal (fun e he ↦
      specializes_iff_forall_open.2 fun O p a ↦ (hW.exists_basicOpen_le (V := ⟨O, p⟩) ⟨_, a⟩ ((H
      he).2 ⟨⟩)).elim fun f ⟨l, a⟩ ↦ l ((landsIn_basicOpen (H hb).2 f).2 ((D f).mp (o.inter_closure
      ⟨hb, (Filter.not_eventually.1 (((A f).eqOn_zero_of_preconnected_of_eventuallyEq_zero k.2 hb ·
      he).mt ((landsIn_basicOpen (H he).2 f).1
      (landsIn_iff_mem.2 a)).ne_zero)).mem_closure⟩)).2.isUnit ⟨⟩)) o m⟩
  (K u c ⟨subset_closure m, m⟩).imp fun _ ⟨v, e⟩ ↦ ⟨v, (n.2.subset_of_closure_inter_subset
    isOpen_interior ⟨c, m, e⟩ (K isOpen_interior · · |>.elim fun d ⟨v, e⟩ ↦ interior_mono
    (fun _ ↦ Specializes.trans (interior_subset v)) e)).trans interior_subset⟩

omit s
variable {Z ι} {X Y S : Scheme} {ξ : Z → (_ ⟶ X)} {η : Z → (Spec _ ⟶ S)} [Finite ι] {v : Z → ι → ℂ}

lemma IsDenseFamily.surjective (h : IsDenseFamily ξ) f [@UniversallyClosed Y X f] (y : Z → _) (H :
  ∀ z, y z ≫ f = ξ z) :
  Surjective f := ⟨isClosed_property h f.isClosedMap.isClosed_range (⟨_, congr($(H ·) _)⟩)⟩

namespace IsSeparatingFamily

/-- Let the complex points ξ_z of X be separating (`IsSeparatingFamily`). Two functions regular on
an open U that agree at all ξ_z lying in U agree at every ring-valued point of U. -/
lemma pointFn_ext (hξ : IsSeparatingFamily ξ) {U f g} (hf : IsRegularOn f U) (hg : IsRegularOn g U)
  (h : ∀ z, LandsIn (ξ z) U → f _ (ξ z) = g _ (ξ z)) A t : LandsIn t U → f A t = g A t :=
  by_contra fun _ ↦ have ⟨_, x⟩ := hξ.2.exists_mem_open (X.basicOpen (hf.exists_ofSection.choose -
    hg.exists_ofSection.choose)).2 (by simp [nonempty_iff_ne_empty, hξ.1]; grind)
  by grind [landsIn_iff_mem.2 x, landsIn_basicOpen, ofSection_eq, LandsIn.mono, X.basicOpen_le,
    isUnit_iff_ne_zero]

variable {X G : Over S} {e : ∀ z, mk (η z) ⟶ X} (he : IsSeparatingFamily (e · |>.left)) {p : ∀ z,
  mk (η z) ⟶ G}
include he

lemma hom_ext [IsSeparated G.hom] {f g : X ⟶ G} (h : ∀ z, e z ≫ f = e z ≫ g) : f = g := have := he.1
  have := he.2.surjective _ _ (congr($(lift_ι _ <| h ·).1))
  by ext; exact ext_of_isDominant_of_isSeparated G.hom (by simp) _ congr($(condition f g).1)

/-- Let e_z, p_z be complex points of S-schemes X, G over the same η_z, with X reduced and the e_z
dense. If a linear system W on X and a projective embedding M of G give e_z, p_z the same
homogeneous coordinates, then some S-morphism d : X → G has d∘e_z = p_z and d^*M = W. -/
lemma exists_map_of_coords {W M} (hW : IsLinearSystem W) (hM : IsProjEmbedding M G.hom) (h : ∀ z,
  W.IsHomogCoords (e z).1 (v z)) (k : ∀
  z, M.IsHomogCoords (p z).1 (v z)) : ∃ d, (∀ z, e z ≫ d = p z) ∧ M.pull d.left = W := by
  obtain ⟨⟨f, b, rfl⟩, ⟨_, D⟩, j, _, a, rfl⟩ := hW.exists_hom_projSpace X.hom,
    he, hM.exists_isClosedImmersion
  have E z : _ ≫ j = _ ≫ f := isProjEmbedding_projSpace.eq_of_isHomogCoords (by aesop) (k z) (h z)
  obtain ⟨d, rfl⟩ :=
    exists_lift_of_dense_preimage j f (D.mono (forall_mem_range.2 (⟨_, congr($(E ·) _)⟩)))
  exact ⟨homMk d, by simp_all [OverMorphism.ext_iff, ← cancel_mono j]⟩
