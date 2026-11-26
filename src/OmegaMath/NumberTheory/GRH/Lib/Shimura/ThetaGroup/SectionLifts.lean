import OmegaMath.NumberTheory.GRH.Lib.Cohomology.Etale.TestRings
import OmegaMath.NumberTheory.GRH.Lib.General.Geometry.ConstantFunctions
import OmegaMath.NumberTheory.GRH.Lib.Shimura.IntegralModel.GroupBaseChange
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Theta group of an ample line bundle: span of sections, K(L), symmetric theta structures
(known result; see Lib.Shimura.ThetaGroup.RigidFibres).

Part of: Abelian schemes: isogenies finite flat, [m]*L = L^{m²}, Cartier, unramified torsion (known
result; see Lib.Shimura.AbelianScheme.ThetaFamily).

This file: Quasi-finiteness from ample pull-backs; identities for the pairing: ⟨x+y, z⟩ + ⟨x−y, z⟩ =
2⟨x, z⟩, ⟨mx, y⟩ = m⟨x, y⟩ for natural m, symmetry, and compatibility with additive maps; [m]*L =
L^(m²). Maps on
sections induced by isomorphisms of pulled-back line bundles; composition, uniqueness. -/

open CategoryTheory Over AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory AffineSpace
  LineBundle Pic IsFinite MorphismProperty
variable {S : Scheme} {A B T : Over S}

/-- Let N be a linear system separating the points of A, proper over S, and let B be separated
over S. An S-morphism f : A → B with f^*c = m[N] for some c in Pic B and m ≠ 0 is locally
quasi-finite. -/
lemma locallyQuasiFinite_of_pull_picClass [IsSeparated B.hom] {ι c m} {N : LineBundle _ ι} (h :
  N.IsProjEmbedding A.hom) {f : A ⟶ B} (hm : m ≠ 0) (hf : .pull f.left c = m • N.picClass) :
  LocallyQuasiFinite f.1 := by
  have H@⟨h, _, _⟩ := h.pow hm
  refine locallyQuasiFinite_iff_isFinite_fiber.2 fun _ ↦ ((fun {p s} (w : IsPullback p s f.1 _)
    [IsProper s] ↦ iff_isProper_and_isAffineHom.2 ⟨‹_›, ?_⟩) (.of_hasPullback ..) :)
  obtain ⟨u, hu⟩ := exists_isFrame_of_picClass_eq_zero (by
    simpa [c.pull_comp, ← picClass_pow, eq_zero_of_isLocalRing, *] using congr(c.pull $w.w))
  choose c _ using (hu.exists_eq_mul <| (h.pull _).isSection ·)
  rw [← homOfVector_over s c] at *
  have := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨by grind [IsProper.of_comp],
    ⟨fun x y e ↦ w.hom_ext
    (H.ext ((h.pull _).ext_of_transition_eq_mul (h.pull _) (by simp at *; grind [→ transition_self,
    =_ homOfVector_appTop_coord s c, PointFn.ofSection_appTop])) (by grind [w, w.w])) (e =≫ _)⟩⟩
  infer_instance

variable [AddObj A] {c : Pic A.left} {S'} (b : S' ⟶ S) {O} [CommRing O] [ModuleObj O A] (h :
  c.ParallelogramLaw) (x y z : T ⟶ A) (m : ℕ)
include h

lemma Pic.ParallelogramLaw.pairing_add_add_pairing_sub : c.pairing (x + y) z + c.pairing (x - y)
  z = 2 • c.pairing x z := by grind [pairing, ParallelogramLaw, sub_add_eq_add_sub]

/-- If c in Pic A satisfies the parallelogram law on a commutative group scheme A over S, then
⟨mx, y⟩ = m⟨x, y⟩ in Pic T for T-points x, y and natural m, where ⟨x, y⟩ = (x+y)^*c − x^*c −
y^*c + 0^*c. -/
lemma Pic.ParallelogramLaw.pairing_nsmul_left : c.pairing (m • x) y = m • c.pairing x y :=
  m.twoStepInduction (by simp [pairing])
  (by simp) (by grind [pairing_add_add_pairing_sub, add_sub_cancel_right, succ_nsmul])

lemma Pic.ParallelogramLaw.nsmul_class_pairing : (m • c).pairing x y =
  c.pairing (m • x) y := by simp [↓h.pairing_nsmul_left, pairing, atPoint, smul_sub]

omit h

lemma isGroupBaseChange_counit : IsGroupBaseChange b (A := A) ((mapPullbackAdj b).counit A) :=
  ⟨.of_hasPullback .., (AddEquiv.linearEquiv O (.symm ⟨Adjunction.homEquiv .., _⟩)).isLinear⟩

lemma pairing_comm : c.pairing x y = c.pairing y x := by grind [pairing]

lemma pairing_comp [AddObj B] (f : B ⟶ A) [IsAdditive f] (x y : T ⟶ _) : (c.pull f.left).pairing x
  y = c.pairing (x ≫ f) (y ≫ f) := by simp [pairing, Pic.atPoint, ← c.pull_comp, ← comp_left]

instance [IsProper A.hom] [IsProper B.hom] : IsProper (A ⊗ B).hom := by simp; tauto

noncomputable instance [i : IsAbelianScheme B] :
  IsAbelianScheme (pullback b B) := have h := isGroupBaseChange_counit b
  @.mk _ _ _ (of_isPullback h.1 i.2) (of_isPullback h.1 i.3) (of_isPullback
                          (.of_bot (by simp_rw [w, h.1]) (h.nsmul_id_comp _).symm h.1) <| i.4 · ·)

variable {R} {A : Over (Spec R)} [IsLocalRing R] [AddObj A] {c : Pic A.left}

omit [AddObj A] in
@[simp] lemma atPoint_section {T} z : c.atPoint (toUnit T ≫ z) = 0 := by simp [Pic.atPoint,
  c.pull_comp, eq_zero_of_isLocalRing]

@[simp] lemma atPoint_zero {T} : c.atPoint (T := T) 0 = 0 := atPoint_section _

/-- Let A be a commutative group scheme over a local ring and c a symmetric class in Pic A
satisfying `Pic.ParallelogramLaw`. Then the pull-back of c under multiplication by a natural number
m is m²c.

Known result: Abelian schemes: isogenies finite flat, [m]*L = L^{m²}, Cartier, unramified
torsion. -/
lemma pull_nsmul_eq_sq_smul (h : c.ParallelogramLaw) (m : ℕ) : .pull (m • 𝟙 A).left c = m ^ 2 • c :=
  m.rec atPoint_zero fun m ih ↦ by
  linear_combination (norm := (simp [pairing, add_smul]; simp [Pic.atPoint]; module))
    ih + h.pairing_nsmul_left (𝟙 A) (𝟙 _) m + m • h (𝟙 A) (𝟙 _)

open PointFn Spec AddMonObj
variable {R : _} {R' R''} [CommRing R] [CommRing R'] [CommRing R''] {X X' : Over _} {ι κ} (L' :
  LineBundle X'.left κ) (L : LineBundle _ ι) (f) (Φ : L.H0 R → L'.H0 R') {Y} (F : Y ⟶ X) (h :
  L.IsLinearSystem) {N : LineBundle Y.1 κ}
  (φ : R →+* R') (hf : f ≫ X.hom = X'.hom ≫ map (CommRingCat.ofHom φ)) {M} (e : M = L.pull f)

/-- The condition that u is an isomorphism f^*L ≅ L' (a frame of L' ⊗ f^*L⁻¹) and that Φ on
global sections is pull-back along f followed by u. -/
@[simp] def IsPullbackVia u := (L'.mul (L.pull f).inv).IsFrame u ∧ ∀ s i a B t, LandsIn t (L'.opens
  i) → LandsIn (t ≫ f) (L.opens a) → (Φ s).1 i B t = u (i, a) B t * s.1 a B (t ≫ f)

/-- The condition that the map Φ : H⁰(L) → H⁰(L') is pull-back along f : X' → X followed by some
isomorphism f^*L ≅ L'. -/
def IsSectionLift := ∃ u, IsPullbackVia _ L f Φ u

/-- The R-linear endomorphism Φ of H⁰(L) is pull-back along the translation t_z by the section z
followed by some isomorphism t_z^*L ≅ L. -/
abbrev IsTranslationLift [AddObj X] z (Φ : Module.End R (L.H0 R)) :=
  IsSectionLift L L (translation z).left Φ

variable {L' L f Φ}

/-- For a linear system L on an R-scheme and an index j, the j-th coordinate as an element of
the R-module H⁰(L) of global sections. -/
def coordSection j := (⟨_, h.isSection j, (h.1 · j |>.2)⟩ : L.H0 R)

lemma H0_ext {r s : L.H0 R} (h : ∀ {i}, (r.1 i).IsRegularOn (L.opens i) →
  (s.1 i).IsRegularOn (L.opens i) → ∀ B t, LandsIn t (L.opens i) → r.1 i B t = s.1 i B t) : r =
  s := by ext; grind [r.2.symm, s.2.symm, IsSection]

@[local simp] lemma H0_smul (a : R) (s : L.H0 R) i B t :
    (a • s).1 i B t = (preimage (t ≫ X.hom)).hom a * s.1 i B t := rfl

lemma IsSectionLift.picClass_eq : IsSectionLift _ L f Φ → L'.picClass = L.picClass.pull f :=
  (picClass_eq_iff.2 ⟨_, ·.choose_spec.1⟩)

/-- For f : X' → X lying over the ring map φ : R → R' and M = f^*L, the φ-semilinear pull-back
of global sections H⁰(L) → H⁰(M). -/
@[simps! apply_coe] noncomputable def pullSections : L.H0 R →ₛₗ[φ] M.H0 R' := by
  use! (⟨_, ·.2.imp (e ▸ ·.pull f) (e ▸ by tauto)⟩) <;> intros <;> ext <;>
    simp_all; simp [← Category.assoc]

lemma exists_isPullbackVia u (h : (N.mul (L.pull F.1).inv).IsFrame u) : ∃ Φ : _ →ₗ[R] _,
  IsPullbackVia N L F.1 Φ u := by
  choose r hr e _ using fun s : L.H0 R ↦ by simpa using exists_section_mul (𝟙 _) h.1 (s.2.1.pull _)
  use! (⟨_, hr ·⟩), ?_, ?_, h, e <;> exact fun _ _ ↦ H0_ext (·.ext_of_dominant (𝟙 _) · (L.pull F.1)
    fun a ↦ by simp +contextual [e _ _ a, mul_add, mul_left_comm])

lemma exists_isSectionLift : N.picClass = L.picClass.pull F.1 → ∃ Φ : _ →ₗ[R] _,
  IsSectionLift N L F.1 Φ := (exists_comm.1 <| picClass_eq_iff.1 · |>.imp (exists_isPullbackVia F))

attribute [local simp] IsFrame IsSection IsRegularOn

lemma IsSectionLift.pull_eq_of_coordSection {L'} h' {Φ a} : IsSectionLift L' L f Φ →
  (∀ j, Φ (_root_.coordSection h j) = (a : R') • _root_.coordSection h' j) → L.pull f =
  L' | ⟨_, _, H⟩, e => h'.ext_of_transition_eq_mul (h.pull f) (by
         have := (e · ▸ H _); simp [_root_.coordSection,
           isUnit_iff_exists_inv] at *; grind [transition_self])

/-- Let L be a linear system, F : Y → X an R-morphism, and s_j sections of N, locally one of them a
unit, proportional to the coordinates of F^*L. Then some R-linear lift Φ : H⁰(L) → H⁰(N) of F sends
the j-th coordinate to s_j. -/
lemma exists_isSectionLift_coordSection {s : ι → N.H0 R} (H : ∀ i a B t, LandsIn t (N.opens i) →
  LandsIn (t ≫ F.1) (L.opens a) → (∃ j, IsUnit ((s j).1 i B t)) ∧ ∀ j, (s j).1 i B t =
  (s a).1 i B t * L.transition a j B (t ≫ F.1)) : ∃ Φ : _ →ₗ[R] _, IsSectionLift N L F.1 Φ ∧ ∀ j,
  Φ (_root_.coordSection h j) = s j := have := (s · |>.2.1)
  (exists_isPullbackVia F (fun (i, a) ↦ (s a).1 i) (by simp_all; grind)).imp fun Φ E ↦
                   ⟨⟨_, E⟩, fun j ↦
    H0_ext (·.ext_of_dominant (𝟙 _) · (L.pull F.1) (by simp; grind [_root_.coordSection, E.2]))⟩

lemma isSectionLift_pullSections : IsSectionLift M L f (pullSections φ hf e) := by
  use M.transition.uncurry; simp_all [L.regular _ _ _, transition_trans, isUnit_transition,
    mul_right_comm]; rintro _ ⟨⟨⟩⟩; tauto

lemma pullSections_coordSection i : pullSections φ hf e (_root_.coordSection h i) =
  _root_.coordSection (e ▸ h.pull f) i := by aesop

/-- Lifts compose: if Φ: H⁰(L) → H⁰(L') is pull-back along f followed by an isomorphism f^*L ≅
L', and Θ: H⁰(L') → H⁰(L'') likewise along g, then Θ∘Φ is such a map along f∘g: X'' → X. -/
lemma IsSectionLift.comp {X'' μ L'' g Θ} : @IsSectionLift _ R'' _ _ _ X'' _ μ L'' _ g Θ →
  IsSectionLift _ L f Φ → IsSectionLift _ L (g ≫ f) (Θ ∘ Φ) := by
  rintro ⟨v⟩ ⟨u⟩; simp at *
  refine (exists_section_mul (𝟙 _) (u := fun ((i, a), b) ↦ v (i, b) * (u (b, a)).pull g) (.left ?a)
    (by simp : IsSection (mk _ 1 (L'.pull g).3) 1)).imp fun w H ↦ ⟨H.2.2 ?a (by simp), fun s i
    a ↦ by simpa using ((Θ _).2.1.1 i).mono (by simp; order) |>.ext_of_dominant (𝟙 _) ((H.1.1.1 (i,
    a)).mul ((s.2.1.1 a).pull (g ≫ f))) (L'.pull g) <| by replace H := H.2.1; simp at *; grind⟩
  simp; grind [L'.6]

lemma IsSectionLift.exists_eq_smul {Ψ} [AddObj X'] (hX : HasConstFunctions X'.hom) : IsSectionLift _
  L f Φ → IsSectionLift _ L f Ψ → ∃ c : R', ∀ s, Φ s = c • Ψ s := fun ⟨_, u, _⟩ ⟨_, v, _⟩ ↦
  (v.exists_eq_mul u.1).imp' (PointFn.ofSection · _ ζ[X'].1) fun c _ s ↦ H0_ext (·.ext_of_dominant
  (𝟙 _) · (L.pull f) fun _ _ t ↦ by simp_all [← isRegularOn_ofSection _ _, hX c _ _ t]; grind)

lemma IsSectionLift.injective [IsSchemeTheoreticallyDominant f] [QuasiCompact f] :
  IsSectionLift _ L f Φ → Φ.Injective
  | ⟨_, _⟩, _, _, _ => H0_ext (·.ext_of_dominant f · L' (by simp_all [isUnit_iff_exists]; grind))
