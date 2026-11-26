import GRH.Lib.General.Geometry.PointFunctions
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic geometry (textbook or folklore).

This file: Picard group of a scheme, pull-back, fpqc descent of sections and frames. Projective
space over Z, O(1), linear systems, maps to projective space, projective embeddings. -/

open Int Localization Quotient AlgebraicGeometry CategoryTheory CommRingCat Finset PointFn
  HomogeneousLocalization LandsIn IsLocalization LineBundle MvPolynomial Ring Proj
  CategoryTheory.Limits MorphismProperty Limits.prod

section

attribute [local grind! .] isRegularOn_ofSection regular LineBundle.transition_trans landsIn_inf

attribute [local simp] IsRegularOn IsFrame IsSection

variable {X Y Z ι κ A} {L : LineBundle X ι} {M : LineBundle X κ} {u s} (hu : L.IsFrame u) (hs :
  L.IsSection s)
  (K : LineBundle X ι) (p π : Y ⟶ X) (q : Z ⟶ Y) [Flat π] [Surjective π] [QuasiCompact π] {i j : ι}

lemma LineBundle.isUnit_transition {t} : LandsIn t (K.opens i) → LandsIn t (K.opens j) →
  IsUnit (K.transition i j A t) := by grind [K.5, → K.6]

@[simp] lemma LineBundle.pull_comp : K.pull (q ≫ p) = (K.pull p).pull q := rfl

@[simp] lemma LineBundle.pull_id : K.pull (𝟙 X) = K := rfl

/-- For π: Y → X flat, surjective, quasi-compact, sections s of L and u of π*(M ⊗ L⁻¹), u
constant on fibres of π, some section r of M, r_i zero off U_i, has r_i(πt) =
u_(i,a)(t)·s_a(πt) whenever πt lands in U_i and V_a. -/
lemma LineBundle.exists_section_mul {u} (hu : ((M.mul L.inv).pull π).IsSection u) (hs :
  L.IsSection s) (H : ∀ i B t s, t ≫ π = s ≫ π → LandsIn (t ≫ π) ((M.mul L.inv).opens i) → u i B t =
  u i B s := by simp) : ∃ r, (M.IsSection r ∧ ∀ i A t, ¬LandsIn t (M.opens i) → r i A t = 0) ∧
  (∀ i a A t, LandsIn (t ≫ π) (M.opens i) → LandsIn (t ≫ π) (L.opens a) → r i A (t ≫ π) =
  u (i, a) A t * s a A (t ≫ π)) ∧ (((M.mul L.inv).pull π).IsFrame u → L.IsFrame s → M.IsFrame r) :=
  (Classical.skolem.1 fun i ↦ exists_ofSection_glue π (L.pull π) (u.curry i * PointFn.pull π
  ∘ s) (by simp_all) (by simp_all; grind)).imp' (ofSection <| · ·) fun r K ↦
  (fun e ↦ ⟨⟨e, fun _ _ _ ↦ (dite_eq_right ·)⟩, K,
    fun _ _ ↦ ⟨e, fun i _ _ h ↦ (landsIn_basicOpen h _).1
  (h.mono (π.surjective.forall.2 (le_of_cover (L.pull π) (by simp_all [↓landsIn_preimage]; grind
  [landsIn_basicOpen]) : π ⁻¹ᵁ _ ≤ π ⁻¹ᵁ X.basicOpen _)))⟩⟩) ⟨by grind, by
  intros; apply (((isRegularOn_ofSection _).mono _).ext_of_dominant π ((regular ..).mul
    (isRegularOn_ofSection _)) (L.pull π)) <;> simp_all [inf_assoc]; grind⟩

/-- fpqc descent: a line bundle L on X has a nowhere vanishing global section if its pull-back
along a flat, surjective, quasi-compact π: Y → X has one whose values at ring-valued points
depend only on their images under π. -/
lemma LineBundle.exists_isFrame_of_fpqc {u} (hu : (L.pull π).IsFrame u) (H : ∀ i B t s, t ≫ π =
  s ≫ π → LandsIn (t ≫ π) (L.opens i) → u i B t = u i B s) : ∃ s, L.IsFrame s := by
  apply (@exists_section_mul _ _ _ _ one _ 1 π _ _ _ (u ·.1) ..).imp fun _ e ↦ e.2.2 ?_ ?_ <;> aesop

lemma LineBundle.IsIsomorphic.refl : K.IsIsomorphic K :=
  ⟨K.transition.uncurry, by simp; grind [isUnit_transition, IsRegularOn]⟩

lemma LineBundle.IsIsomorphic.exists_isFrame : L.IsIsomorphic M → Exists M.IsFrame →
  Exists L.IsFrame | ⟨_, h⟩, ⟨_, k⟩ => (exists_section_mul (𝟙 _) h.1 k.1).imp (by tauto)

lemma LineBundle.IsIsomorphic.mul {μ ν N P} : L.IsIsomorphic M → @IsIsomorphic X μ ν N P →
  (L.mul N).IsIsomorphic (M.mul P)
  | ⟨u, _⟩, ⟨v, _⟩ => ⟨fun ((a, b), c, d) ↦ u (a, c) * v (b, d), by simp_all; grind⟩

lemma LineBundle.IsSection.pull (hs : L.IsSection s) (p : Y ⟶ X) :
  (L.pull p).IsSection (s · |>.pull p) := by aesop

namespace LineBundle.IsFrame

include hu

lemma pull : (L.pull p).IsFrame (u · |>.pull p) := by aesop

lemma inv : L.inv.IsFrame (inverse <| u · · ·) := by simp_all; grind

lemma mul {v} : M.IsFrame v → (L.mul M).IsFrame fun i ↦ u i.1 * v i.2 := by simp_all; grind

include hs

/-- If u is a nowhere vanishing section of L, every section s of L is c·u for some global
function c in Γ(X, O_X). -/
lemma exists_eq_mul : ∃ c, ∀ i A t, LandsIn t (L.opens i) → s i A t =
  (@ofSection X ⊤ c * u i) A t := by
  apply (exists_ofSection_glue (𝟙 _) L ((inverse <| u · · ·) * s) ..).imp <;> simp_all <;> grind

end LineBundle.IsFrame

/-- The Picard group of X: line bundles given by cocycles, modulo isomorphism; the group law is
written additively. -/
def Pic X := @Quotient (Sigma (LineBundle X)) ⟨(·.2.IsIsomorphic ·.2), (.refl ·.2),
  (flip LineBundle.IsIsomorphic.exists_isFrame (LineBundle.IsIsomorphic.refl _) <|
  (LineBundle.IsIsomorphic.refl _).mul ⟨_, ·.choose_spec.inv⟩), (·.mul (.refl _) |>.exists_isFrame)⟩

/-- The class of the line bundle K in the Picard group of X. -/
def LineBundle.picClass : Pic X := ⟦⟨ι, K⟩⟧

lemma LineBundle.picClass_eq_of_le (e : κ → ι) (hU : ∀ a, M.opens a ≤ L.opens (e a)) (h : ∀ a b A t,
  LandsIn t (M.opens a) → M.transition a b A t = L.transition (e a) (e b) A t) : L.picClass =
  M.picClass := sound ((IsIsomorphic.refl L).imp' (· ∘ .map id e) (by simp; grind [mono]))

instance : AddCommGroup (Pic X) := by apply @AddCommGroup.mk _ (@.ofRightAxioms _ ⟨.map₂ (⟨_,
  ·.2.mul ·.2⟩) fun _ _ h _ _ ↦ h.mul⟩ ⟨.map (⟨_, ·.2.inv⟩) fun _ _ ⟨_, h⟩ ↦ ⟨_, h.inv⟩⟩
  ⟨one.picClass⟩ ..) <;> (repeat rintro ⟨_, _⟩) <;> (first
  | apply picClass_eq_of_le (by simp; bound) | refine sound ((LineBundle.IsIsomorphic.refl ‹_›).imp'
    (· ∘ .fst) ?_)) <;> simp [inf_assoc] <;> grind

lemma LineBundle.picClass_eq_iff : L.picClass = M.picClass ↔ L.IsIsomorphic M := eq

@[simp] lemma LineBundle.picClass_mul : (L.mul M).picClass = L.picClass + M.picClass := rfl

lemma LineBundle.exists_isFrame_of_picClass_eq_zero : L.picClass = 0 → Exists L.IsFrame :=
  (exact · |>.exists_isFrame ⟨1, by simp⟩)

/-- For p: Y → X, the homomorphism Pic X → Pic Y sending the class of a line bundle to the class
of its pull-back. -/
noncomputable def Pic.pull : Pic X →+ Pic Y := .mk'
    (.map (⟨_, ·.2.pull p⟩) fun _ _ ⟨_, h⟩ ↦ ⟨_, h.pull p⟩) (by rintro ⟨⟩ ⟨⟩; rfl)

@[simp] lemma Pic.pull_picClass : pull p K.picClass = (K.pull p).picClass := rfl

lemma Pic.pull_comp c : pull (q ≫ p) c = pull q (pull p c) := c.out_eq ▸ rfl

@[simp] lemma Pic.pull_id c : pull (𝟙 X) c = c := c.out_eq ▸ rfl

lemma Pic.eq_zero_of_isLocalRing (c : Pic (Spec A)) [IsLocalRing A] : c = 0 := c.ind' fun _ ↦
    (exists_landsIn _ (𝟙 _)).elim fun i h ↦
  picClass_eq_of_le _ (by tauto) (by simp [transition_self _ _ _ _ (mono _ h)])

end

lemma eval₂_mul_of_isHomogeneous {σ R S} [CommRing R] [CommRing S] {n a} (h : @IsHomogeneous σ R _ a
    n) f (c : S) v : eval₂ f (c * v ·) a = c ^ n * eval₂ f v a := by simp +contextual [eval₂_eq,
  mul_sum, mul_pow, mul_left_comm, prod_pow_eq_pow_sum, ← h.degree_eq_sum_deg_support]

lemma ProjSpace.X_mem_homogeneousSubmodule {ι : Type} (i : ι) : .X i ∈ homogeneousSubmodule ι ℤ 1 :=
  isHomogeneous_X ..

attribute [local instance] gradedAlgebra

/-- Projective space over ℤ with homogeneous coordinates X_i, i in ι: the scheme Proj ℤ[X_i]. -/
noncomputable abbrev ProjSpace ι := Proj (homogeneousSubmodule.{0} ι ℤ)

variable {X ι A} (L : LineBundle X ι) (t : Spec A ⟶ X) (v : ι → A) (i j : ι) {L' M : LineBundle X ι}

/-- The function X_j/X_i on ring-valued points of projective space landing in D₊(X_i), and zero
at the other points. -/
noncomputable abbrev ProjSpace.coordRatio := ofSection (awayToSection _ _
  (.isLocalizationElem (X_mem_homogeneousSubmodule i) (X_mem_homogeneousSubmodule j)))

@[simp] lemma ProjSpace.coordRatio_mul (k : ι) t (h : LandsIn t (basicOpen _ (.X i) ⊓ basicOpen _
  (.X j))) : coordRatio i j A t * coordRatio j k A t = coordRatio i k A t := by
  simpa [← ofSection_map _ ⟨⟨⟨_⟩⟩⟩ h, ↓ofSection_eq h, ← map_mul] using congrArg _
    (Subtype.ext (by ext; exact mk_eq_mk_iff.2 (r_of_eq (by simp [mul_assoc]))))

/-- The line bundle O(1) on projective space, with the standard cover D₊(X_i) and transition
functions X_j/X_i. -/
noncomputable def ProjSpace.hyperplaneBundle ι : LineBundle (ProjSpace ι) ι :=
  .mk _ coordRatio (iSup_basicOpen_eq_top' _ _ (⟨1, X_mem_homogeneousSubmodule ·⟩)
  (by rw [← Algebra.adjoin_adjoin_of_tower ℤ]; simp)) (by simp [(isRegularOn_ofSection _).mono])
  fun i ↦ by simp_all [ofSection_eq, (by aesop :
  Away.isLocalizationElem (X_mem_homogeneousSubmodule i) (X_mem_homogeneousSubmodule i) = 1)]

lemma ProjSpace.isAffineOpen_chart : IsAffineOpen ((hyperplaneBundle ι).opens i) :=
  isAffineOpen_basicOpen _ _ (X_mem_homogeneousSubmodule i) .refl

/-- v gives homogeneous coordinates of the A-valued point t: t lands in U_j exactly when v_j is
a unit of A, and then g_jk(t) = v_k/v_j for all k. -/
def LineBundle.IsHomogCoords := ∀ j, (LandsIn t (L.opens j) ↔ IsUnit (v j)) ∧ ∀ k, IsUnit (v j) →
  L.transition j k A t = v k * (v j)⁻¹ʳ

/-- L is a linear system: each g_ij is regular on U_i, zero off U_i, a unit only on U_j, and
g_ij = g_ik g_kj on U_i ∩ U_k. -/
def LineBundle.IsLinearSystem := (∀ i j, (L.transition i j).IsRegularOn (L.opens i) ∧ ∀ A t,
  ¬LandsIn t (L.opens i) → L.transition i j A t = 0) ∧
  ∀ {i A t}, LandsIn t (L.opens i) → L.IsHomogCoords t (L.transition i · A t)

/-- The line bundle O(1) on projective space Proj ℤ[X_i], i in ι, with the standard cover
D₊(X_i) and transition functions X_j/X_i, is a linear system in the sense of
`LineBundle.IsLinearSystem`. -/
lemma ProjSpace.isLinearSystem_hyperplaneBundle : (hyperplaneBundle ι).IsLinearSystem :=
  ⟨fun _ _ ↦ ⟨isRegularOn_ofSection _, fun _ _ ↦ (dite_eq_right ·)⟩, fun {i _ _} h _ ↦
  (⟨·, by simp_all [hyperplaneBundle, eq_mul_inverse_iff_mul_eq, mul_comm _ (coordRatio i ..)]⟩)
  ⟨isUnit_transition _ h, fun u _ hx ↦ by simpa using!
  ((ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply _ ⟨_, h hx⟩ _).2.mt ((((hyperplaneBundle
  ι).opens i).toSpecΓ_preimage_basicOpen _).ge ((landsIn_basicOpen h _).2 u hx)))⟩⟩

attribute [local simp, local grind] IsRegularOn LandsIn.comp IsLinearSystem IsSection IsHomogCoords

lemma LineBundle.IsLinearSystem.ext_of_transition_eq_mul (h : L'.IsLinearSystem) (hM :
  M.IsLinearSystem) (H : ∀ i j k A t, LandsIn t (L'.opens i) → LandsIn t (M.opens j) → M.transition
  j k A t = M.transition j i A t * L'.transition i k A t) : M = L' := (LineBundle.ext · (by grind))
  (by ext1; apply le_antisymm <;> grind [le_of_cover L', le_of_cover M])

lemma LineBundle.IsLinearSystem.isSection (h : M.IsLinearSystem) :
  M.IsSection (M.transition · j) := by grind

variable {Y} {ι : Type} {A : CommRingCat} {L : LineBundle X ι} {v : ι → A} {p : Y ⟶ X} (p : Y ⟶ X)

lemma LineBundle.IsLinearSystem.pull (h : L.IsLinearSystem) :
  (L.pull p).IsLinearSystem := by simp; grind

variable {κ} {A : CommRingCat} {L : LineBundle X ι} {N : LineBundle X κ} {t : Spec A ⟶ X} {v : ι →
  A} {S} {s : X ⟶ S} (p : Y ⟶ X)

lemma LineBundle.IsLinearSystem.mul (h : L.IsLinearSystem) : N.IsLinearSystem →
  (L.mul N).IsLinearSystem := by simp; grind

lemma LineBundle.IsHomogCoords.pull_iff {p : Y ⟶ X} {t} : (L.pull p).IsHomogCoords t v ↔
  L.IsHomogCoords (t ≫ p) v := .rfl

lemma LineBundle.IsHomogCoords.smul (l : L.IsHomogCoords t v) {u : A} : IsUnit u →
  L.IsHomogCoords t (u • v) := by simp; grind

lemma LineBundle.IsHomogCoords.map {i : ι} {L : LineBundle X ι} {t : Spec A ⟶ X} {v : ι → A} (l :
  L.IsHomogCoords t v) {R} :
  L.IsLinearSystem → IsUnit (v i) → ∀ φ, L.IsHomogCoords (@Spec.map A R φ ≫ t) (φ ∘ v) := by grind

lemma LineBundle.IsHomogCoords.mul (l : L.IsHomogCoords t v) {w} :
    N.IsHomogCoords t w → (L.mul N).IsHomogCoords t fun i ↦ v i.1 * w i.2 := by simp; grind

lemma LineBundle.IsHomogCoords.ne_zero (l : L.IsHomogCoords t v) [IsLocalRing A] :
    ∃ i, v i ≠ 0 := (L.exists_landsIn t).imp (by aesop)

/-- A vector v in A^ι with some entry v_i a unit is a vector of homogeneous coordinates of some
A-valued point of projective space. -/
lemma ProjSpace.exists_isHomogCoords {S : Scheme} {ι : Type} {A : CommRingCat} {i : ι} {v : ι →
  A} (b : _ ⟶ S) (h : IsUnit (v i)) : ∃ s, s ≫ snd = b ∧
  ((hyperplaneBundle ι).pull fst).IsHomogCoords s v := ⟨_, lift_snd .., by
  rw [IsHomogCoords.pull_iff, lift_fst]; convert!
    (isLinearSystem_hyperplaneBundle.2 (landsIn_fromSpec (isAffineOpen_chart i) (Spec.map
    ((basicOpenIsoAway _ _ (X_mem_homogeneousSubmodule i) .refl).2 ≫ ofHom
    ((awayLift (eval₂Hom (castRingHom _) v) (X i) (by simpa)).comp (algebraMap ..)))))).smul
    h; ext; dsimp [hyperplaneBundle, coordRatio]; erw [ofSection_map_fromSpec,
    comp_apply, Iso.hom_inv_id_apply, awayLift_mk (v := h.unit.2), mul_left_comm] <;> simp⟩

/-- L is a linear system, s: X → S is proper, and morphisms to X with the same composite to S
and the same homogeneous coordinates under L are equal. -/
def LineBundle.IsProjEmbedding {S ι} L (s : X ⟶ S) := IsLinearSystem L ∧ IsProper s ∧
  ∀ {i : ι} {A a b}, (LandsIn a (L.opens i) ∧ LandsIn b (L.opens i) ∧ ∀ j, L.transition i j A a =
  L.transition i j A b) → a ≫ s = b ≫ s → a = b

/-- If L satisfies `LineBundle.IsProjEmbedding` for s: X → S, two A-valued points of X with the same
image in S and the same homogeneous coordinates v are equal, provided one of them lands in some open
U_i. -/
lemma LineBundle.IsProjEmbedding.eq_of_isHomogCoords {a} (h : L.IsProjEmbedding s) (o : a ≫ s =
  t ≫ s) (x : L.IsHomogCoords a v) (y : L.IsHomogCoords t v) (u : ∃ i,
  LandsIn a (L.opens i) := by apply LineBundle.exists_landsIn) : a = t := by grind [IsProjEmbedding]

protected lemma LineBundle.IsProjEmbedding.of_isPullback {T p t b} : L.IsProjEmbedding s →
  IsPullback p t s b → @IsProjEmbedding Y T _
  (L.pull p) t | ⟨l, o, h⟩, H => ⟨l.pull _, of_isPullback H o, by simp; grind [H.hom_ext, H.w]⟩

/-- For finite κ and any scheme S, the pull-back of O(1) to ℙ^κ × S embeds ℙ^κ × S projectively over
S along the second projection (`LineBundle.IsProjEmbedding`). -/
lemma isProjEmbedding_projSpace [Finite κ] :
  @IsProjEmbedding _ S _ ((ProjSpace.hyperplaneBundle κ).pull fst) snd := .of_isPullback
  ⟨ProjSpace.isLinearSystem_hyperplaneBundle, (specZIsTerminal.hom_ext ..).subst
  (comp_mem _ _ _ (@instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat _ _ _ _ _ _ _
  (.of_restrictScalars_finiteType ℤ ..)) (@instIsProperOfIsFinite _ _ _ ((IsFinite.SpecMap_iff
  _).2 (RingHom.finite_algebraMap.2 (.of_fg (homogeneousSubmodule_fg ..)))))), fun ⟨h, k, e⟩ _ ↦
  map_evalSection_fromSpec (ProjSpace.isAffineOpen_chart _) h ▸ map_evalSection_fromSpec _ k ▸ by
  congr 2; erw [← cancel_epi (basicOpenIsoAway _ _ (ProjSpace.X_mem_homogeneousSubmodule _)
    .refl).1, CommRingCat.hom_ext_iff, ← RingHom.cancel_right (f :=
    eval₂Hom (castRingHom _) _)]; ext <;> simp; repeat erw [← ofSection_eq]
  apply e; intro x; obtain ⟨n, a, ha, rfl⟩ :=
    x.mk_surjective _ (ProjSpace.X_mem_homogeneousSubmodule _)
  use a; ext; rw [← HomogeneousLocalization.algebraMap_apply, map_eval₂Hom]
  simp [mk_eq_mk', eq_mk'_iff_mul_eq, mul_comm, ← eval₂_mul_of_isHomogeneous (by simpa using ha)]
  apply eval₂Hom_X⟩ (.of_is_product' (prodIsProd ..) specZIsTerminal)

/-- Sections s_j (j in κ) of L with no common zero at field points factoring through a
surjective p give a linear system M of the same class, with homogeneous coordinates (s_j),
equal to f*O(1) for some f: X → ℙ^κ. -/
lemma LineBundle.exists_picClass_eq_pull_hyperplane [Finite κ] [o : Surjective p] {s : κ → _} (h :
  ∀ j, L.IsSection (s j)) (k : ∀ i K [Field K] t, LandsIn (t ≫ p) (L.opens i) → ∃ j, s j i ⟨K⟩
  (t ≫ p) ≠ 0) : ∃ f, L.picClass = ((ProjSpace.hyperplaneBundle κ).pull f).picClass ∧ ∀ i A t,
  LandsIn t (L.opens i) → ((ProjSpace.hyperplaneBundle κ).pull f).IsHomogCoords t (s · i A t) := by
  choose W N using fun {j i} ↦ (((h j).1 i).exists_ofSection.imp' X.basicOpen
    (by grind [landsIn_basicOpen, mono, X.basicOpen_le]) : ∃ W, ∀ {A t}, LandsIn t W ↔
    LandsIn t (L.opens i) ∧ IsUnit (s j i A t)); choose F e r using fun {p A t} h ↦
    @ProjSpace.exists_isHomogCoords X _ _ (Prod.snd p) (s · p.1 A t) t (N.1 h).2; refine
    (exists_hom_of_cover (mk _ 1 ?c) @F fun _ q _ _ φ _ a _ ↦ isProjEmbedding_projSpace.2.2 (i :=
    q.2) (have := (r a).map (ProjSpace.isLinearSystem_hyperplaneBundle.pull _) (N.1
      a).2 φ; ?_) ?_).imp' (· ≫ fst) fun _ _ ↦ (⟨picClass_eq_iff.2
    ⟨s.uncurry ∘ .swap, ?_, ·⟩, ?_⟩) fun _ _ _ a ↦ (N.1 (a.mono (le_of_cover (mk _ 1 ?c) ?_))).2
  simpa [SetLike.ext_iff, o.1.forall] using fun x ↦ flip Exists.imp (L.exists_landsIn
    (Y.fromSpecResidueField x ≫ p)) fun i a ↦ (k i _ _ a).imp fun j ↦ (@N.2 ⟨a, ·.isUnit⟩ default)
  all_goals simp at *; grind

/-- A linear system N indexed by κ on X, with any s: X → S, is the pull-back of O(1), cover and
transition functions included, along some morphism X → ℙ^κ × S over S. -/
lemma LineBundle.IsLinearSystem.exists_hom_projSpace [Finite κ] (h : N.IsLinearSystem) (s : X ⟶ S) :
  ∃ j, j ≫ snd = s ∧ ((ProjSpace.hyperplaneBundle κ).pull fst).pull j = N :=
  (exists_picClass_eq_pull_hyperplane (𝟙 _) h.isSection (by grind [transition_self])).imp'
  (prod.lift · s) (by grind [pull_comp, lift_fst, lift_snd, ext_of_transition_eq_mul, pull,
  ProjSpace.isLinearSystem_hyperplaneBundle])

/-- For s: X → S, some linear system on X with finitely many coordinates satisfies
`LineBundle.IsProjEmbedding` for s. -/
@[mk_iff] class inductive HasProjEmbedding (s) : Prop
  | mk {I P} [Finite I] (h : @IsProjEmbedding X S I P s)
