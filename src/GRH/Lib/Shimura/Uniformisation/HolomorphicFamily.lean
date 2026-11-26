import GRH.Lib.Shimura.ComplexTheta.CanonicalMultiplier
import GRH.Lib.Shimura.AbelianScheme.TangentCoords
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Complex uniformisation of PEL abelian varieties; Appell–Humbert; finite class number
(known result; see Lib.Shimura.Uniformisation.AppellHumbert).

This file: Valuation rings of ℂ, holomorphic families of points, jets, uniformisations, theta
coordinates. Holomorphic maps into complex points of schemes: criteria, jets, tangent vectors. -/
seal Finset.univ Finset.sum Finset.prod

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory PointFn

/-- A valuation ring O with fraction field ℂ, together with the generic point `genericPt`, Spec
ℂ → Spec O, induced by O → ℂ. -/
class ValuativeArc O [CommRing.{0} O] extends Algebra O ℂ, IsDomain O, ValuationRing O,
    IsFractionRing O ℂ where
  genericPt : _ ⟶ Spec ⟨O⟩
  genericPt_eq : genericPt = specMap algebraMap := by rfl

attribute [instance 100] ValuativeArc.toAlgebra

instance : ValuativeArc ℂ := ⟨𝟙 _, by simp [specMap]⟩

instance (V : ValuationSubring ℂ) : ValuativeArc V := ⟨_, rfl⟩

/-- The set of complex points of a scheme A over ℂ, that is sections of its structure morphism. -/
abbrev ComplexPoint (A : Over (Spec ⟨ℂ⟩)) := 𝟙_ _ ⟶ A

open ValuativeArc Over OverMorphism UniversallyClosed CartesianMonoidalCategory
variable {O} [CommRing O] [ValuativeArc O] {A : Over (Spec ⟨O⟩)}

instance : IsSchemeTheoreticallyDominant ‹ValuativeArc O›.genericPt := genericPt_eq.substr
  (@.of_isDominant _ _ _ ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by simp)⟩ _)

/-- Valuative criterion of properness: for A proper over a valuation ring O with fraction field
ℂ, every ℂ-point of A above the generic point of Spec O extends uniquely to a section of A
over O. -/
lemma bijective_restrict_genericPt [IsProper A.hom] : (toUnit (Over.mk genericPt) ≫ · : _ →
  (_ ⟶ A)).Bijective := ⟨fun _ _ e ↦ ext (ext_of_isDominant_of_isSeparated A.hom (by simp)
  genericPt congr($e.1) :), (have ⟨⟨l⟩⟩ :=
    (eq_valuativeCriterion.le _ _ _ inferInstance).1 ⟨O, ℂ, _, _, ⟨·.w.trans genericPt_eq⟩⟩
  ⟨homMk _ l.3, ext ((genericPt_eq =≫ _).trans l.2)⟩)⟩

/-- For a family s of sections of A over Spec O, O a valuation ring of ℂ, the complex point of A
given by s(z) at the generic point. -/
def atGeneric {Z} (s : Z → (𝟙_ _ ⟶ A)) (z : Z) : Spec ⟨ℂ⟩ ⟶ A.left :=
  (toUnit (.mk genericPt) ≫ s z).left

@[simp] lemma atGeneric_eq {A Z} (s : Z → ComplexPoint A) : atGeneric s = (s · |>.left) := rfl

variable (A) [AddObj A] {X ι P T M} [FinComplexSpace.{0} P] (V) [FinComplexSpace.{0} V]
  [AddCommGroup M] [Module ℂ M]
  [Module ℂᵐᵒᵖ M] [IsCentralScalar ℂ M] (L) (φ : P → (Spec ⟨ℂ⟩ ⟶ X)) (w₀)

/-- For each open U of X containing φ(w₀) and each f regular on U: φ(w) lies in U for w near w₀,
and the function f∘φ satisfies Q. -/
def HasGermAt [TopologicalSpace T] (Q : (T → ℂ) → _) (φ : T → _) w₀ := ∀ ⦃U f⦄, @IsRegularOn X f U →
  LandsIn (φ w₀) U → (∀ᶠ w in nhds w₀, LandsIn (φ w) U) ∧ Q (f ⟨ℂ⟩ <| φ ·)

/-- The family φ of complex points of X is holomorphic at w₀: functions regular near φ(w₀) pull
back to functions analytic at w₀. -/
abbrev HolomorphicAt := HasGermAt (AnalyticAt ℂ · w₀) φ w₀

/-- τ, a point of X with values in ℂ ⊕ M (M of square zero), satisfies f(τ) = f(φ w₀) + ℓ(d(f∘φ)
at w₀) for every f regular near φ(w₀). -/
def IsJet (ℓ : (P →ₗ[ℂ] ℂ) →ₗ[ℂ] M) τ := ∀ U s, LandsIn (φ w₀) U → LandsIn τ U ∧
  @PointFn.ofSection X U s ⟨TrivSqZeroExt ℂ M⟩ τ =
  .inl (PointFn.ofSection s _ (φ w₀)) + .inr (ℓ (fderiv ℂ (PointFn.ofSection s _ <| φ ·) w₀))

/-- φ is constant to first order at w₀ in the direction v: its derivative there is the zero
tangent vector at φ(w₀). -/
abbrev IsFirstOrderConst v := IsJet φ w₀ (.applyₗ v) (specMap (algebraMap ..) ≫ φ w₀)

/-- φ is a holomorphic immersion at w₀: it is holomorphic there, and constant to first order
only in the direction 0. -/
def IsHolImmersionAt := HolomorphicAt φ w₀ ∧ ∀ v, IsFirstOrderConst φ w₀ v → v = 0

/-- A surjective homomorphism from V to the sections of A over O with kernel a lattice,
holomorphic and immersive on complex points, through which homomorphisms holomorphic at 0
factor ℂ-linearly. -/
structure Uniformisation where
  expMap : V →+ (_ ⟶ A)
  L : Submodule ℤ V
  [isZLattice : IsFullRankLattice L]
  surjective : (⇑expMap).Surjective
  eq_zero_iff z : z ∈ L ↔ expMap z = 0
  immersive z : IsHolImmersionAt (atGeneric expMap) z
  universal {W} [FinComplexSpace W] (γ : W →+ _) : HolomorphicAt (atGeneric γ) 0 → ∃ F : W →L[ℂ] V,
    ∀ z, expMap (F z) = γ z

attribute [instance] Uniformisation.isZLattice

attribute [simp, grind =] Uniformisation.eq_zero_iff

/-- N is a linear system, (L, B, χ) are Appell–Humbert data on P, and theta functions θ_i of
type (B, χ) give homogeneous coordinates θ(z) of each complex point φ(z). -/
structure HasThetaCoords (N : LineBundle X ι) B χ (θ : P → ι → ℂ) where
  isLinearSystem : N.IsLinearSystem
  isAppellHumbert : @IsAppellHumbert P _ L B χ
  mem_thetaSpace i : (θ · i) ∈ B.thetaSpace χ
  hasFieldCoords z : N.IsHomogCoords (φ z) (θ z)

open Limits Filter Topology CommRingCat TrivSqZeroExt Spec LineBundle ContinuousLinearMap Fint
  Matrix
variable {X : _} {Y S} {ι P T : _} {U Q} [FinComplexSpace P] {N :
  LineBundle X ι} [TopologicalSpace T] {s : X ⟶ S} {φ ψ : _ → (_ ⟶ X)} {w₀ : T}

attribute [local simp] IsHomogCoords landsIn_basicOpen algebraMap_eq_inl TrivSqZeroExt.ext_iff
  fderiv_fun_mul Hom.zero_def LandsIn.comp funext_iff IsJet

/-- The class Q of functions consists of functions continuous at w₀ and contains every function
that near w₀ is an analytic function of finitely many members. -/
class GermClass (Q : _ → _) w₀ where
  comp {ι : Type} [Fintype ι] {p : T → ι → ℂ} : (∀ i, Q (p · i)) → ContinuousAt p w₀ ∧
    ∀ {g f}, AnalyticAt ℂ g (p w₀) → g ∘ p =ᶠ[𝓝 w₀] f → Q f

instance : GermClass (ContinuousAt · w₀) w₀ := ⟨fun _ ↦ ⟨by fun_prop, fun _ ↦ .congr (by fun_prop)⟩⟩

namespace HasGermAt

lemma comp_hom (h : HasGermAt Q φ w₀) (f : X ⟶ Y) : HasGermAt Q (φ · ≫ f) w₀ := fun _ _ a ↦
  h (a.pull f)

lemma exists_isHomogCoords (h : HasGermAt Q φ w₀) (hN : N.IsLinearSystem) : ∃ p : T → ι → ℂ,
  (∀ i, Q (p · i)) ∧ ∀ᶠ w in 𝓝 w₀, N.IsHomogCoords (φ w) (p w) := have ⟨i, a⟩ := N.exists_landsIn _
  ⟨_, fun j ↦ (h (hN.1 i j).1 a).2, (h (isRegularOn_ofSection 0) a).1.mono fun _ ↦ hN.2⟩

variable [hQ : GermClass Q w₀] [Finite ι] {R} {p : T → ι → _}

/-- Let Q be a class of germs at w₀ and U an affine open containing φ(w) for w near w₀. If s∘φ
has Q for every section s over U, then `HasGermAt` holds for Q, φ, w₀. -/
lemma of_affine (hU : IsAffineOpen U) (h : ∀ᶠ w in 𝓝 w₀, LandsIn (φ w) U)
    (k : ∀ s, Q (@PointFn.ofSection X U s _ <| φ ·)) : HasGermAt Q φ w₀ := fun V f hf hV ↦ by
  have ⟨H, l, m⟩ := hU.exists_basicOpen_le ⟨_, hV ⟨⟩⟩ (landsIn_iff_mem.1 h.self_of_nhds)
  cases (hf.mono l).exists_ofSection; have ⟨n, G, e⟩ :=
    exists_eq_pow_mul_of_isAffineOpen _ _ hU _ ‹_›
  simp [← (landsIn_iff_mem), h.self_of_nhds] at m
  have c := hQ.1 (k <| ![G, H] ·)
  refine .imp_right (c.2 (((proj 0).analyticAt _).div (((proj 1).analyticAt _).pow n) (by aesop)))
    (eventually_and.1 ((h.and ((c.1.apply_nhds 1).eventually_ne m)).mono fun w _ ↦ ?_))
  have := congr(PointFn.ofSection $e.symm _ (φ w))
  erw [ofSection_eq, map_mul, map_pow, ← ofSection_eq, ofSection_map, ofSection_map,
    ← ofSection_eq] at this <;> simp_all [LandsIn.mono _ l, field]

/-- Let N embed X in projective space over Spec R, all φ(w) lie over one point b, and p(w) be
homogeneous coordinates of φ(w) near w₀, each coordinate function in the germ class Q. Then
regular functions near φ(w₀) pull back into Q. -/
lemma of_isHomogCoords {s b} (hN : @IsProjEmbedding X (Spec R) ι N s) (hp : ∀ i,
  Q (p · i)) (h : ∀ᶠ w in 𝓝 w₀, N.IsHomogCoords
  (φ w) (p w)) (hb : ∀ w, φ w ≫ s = b := by intro; apply Over.w) : HasGermAt Q φ w₀ :=
  h.self_of_nhds.ne_zero.elim fun i a ↦ have ⟨u, _, s, V⟩ := hN.exists_affine_chart i
  have E := (((hQ.1 hp).1.apply_nhds i).eventually_ne a).and h
  of_affine u (E.mono (by aesop)) (s.forall.2 fun F ↦ (hQ.1 hp).2 (.aeval_mvPolynomial (proj ·
  |>.analyticAt _ |>.div ((proj i).analyticAt _) a) (F.map (preimage b).1)) (E.mono (by aesop)))

/-- Let W be proper over R with finitely many jointly monomorphic maps π_l to projective
R-schemes, and φ a family of complex points over one point b. If each π_l∘φ pulls regular
functions into the germ class Q at w₀, so does φ. -/
lemma of_jointly_mono {W : Over (Spec R)} [p : IsProper W.hom] {Z : ι → _} (π : ∀ l, W ⟶ Z l) [e :
  ∀ l, HasProjEmbedding (Z l).hom] (H : ∀ {T} {x y : T ⟶ W}, (∀ l, x ≫ π l = y ≫ π l) → x =
  y) {φ b} (h : ∀ l, HasGermAt Q (φ · ≫ (π l).left) w₀) (o : ∀ w, φ w ≫ W.hom =
  b := by intro; apply Over.w) : HasGermAt Q φ w₀ := by
  choose ν N _ hN using ((hasProjEmbedding_iff _).1 <| e ·)
  choose p hp k using (h · |>.exists_isHomogCoords (hN _).1)
  exact of_isHomogCoords (isProjEmbedding_pi π hN H) (fun i ↦ (hQ.1 (hp · (i _))).2
    (g := (∏ l, · l)) (ContDiffAt.analyticAt (by fun_prop)) .rfl) (.mono (.all k) (by
    simp_all [landsIn_iInf, Finset.prod_eq_zero_iff])) o

lemma lift {A N} (e : @IsProjEmbedding _ _ ι N A.hom) {φ ψ : _ → ComplexPoint A} (h :
  HasGermAt Q (φ · |>.left) w₀) (h' : HasGermAt Q (ψ · |>.left) w₀) : HasGermAt Q
  (fun w ↦ (CartesianMonoidalCategory.lift (φ w) (ψ w)).left) w₀ := of_jointly_mono (p := e.2.rec
  (by simp; tauto)) ![fst A A, snd A A] (e := fun _ ↦ ⟨e⟩) (by aesop) (by simp [↓← comp_left, *])

end HasGermAt

variable {w₀ : P} {V M A : _} [FinComplexSpace V] [AddObj A] (u : Uniformisation (O := ℂ) A V)
  [AddCommGroup M] [Module ℂ M] [Module ℂᵐᵒᵖ M] [IsCentralScalar ℂ M] {ℓ τ τ' v₀ b v g'} {g : V → P}

instance : GermClass (AnalyticAt ℂ · w₀) w₀ :=
  ⟨fun h ↦ ⟨(AnalyticAt.pi h).continuousAt, (·.comp (.pi h) |>.congr)⟩⟩

namespace IsJet

variable (h : IsJet (M := M) φ w₀ ℓ τ)
include h

lemma unique : IsJet φ w₀ ℓ τ' → τ = τ' := have ⟨U', a⟩ := exists_isAffineOpen_landsIn (φ w₀)
  (by apply point_eq_of_ofSection_eq a.1 <;> simp_all [h U' 0, · U' 0])

lemma comp_hom (p : X ⟶ Y) : IsJet (φ · ≫ p) w₀ ℓ (τ ≫ p) := (h _ <| p.app · ·)

lemma congr (e : φ =ᶠ[𝓝 w₀] ψ) : IsJet ψ w₀ ℓ τ :=
  (by erw [← (e.fun_comp _).fderiv_eq, ← e.eq_of_nhds]; apply h · ·)

lemma fst_comp : specMap (fstHom ℂ ℂ M).1 ≫ τ =
  φ w₀ := have ⟨U', a⟩ := exists_isAffineOpen_landsIn (φ w₀)
  by apply point_eq_of_ofSection_eq a.1 <;> simp_all [isRegularOn_ofSection _ _, h U' 0]

lemma comp_base_eq (e : ∀ w, φ w ≫ s = b) : τ ≫ s = specMap (algebraMap ..) ≫ b :=
  (h.comp_hom s).unique (by simp_all [isRegularOn_ofSection _ _])

end IsJet

lemma HolomorphicAt.comp (h : HolomorphicAt φ (g v₀)) (hg : AnalyticAt ℂ g v₀) :
  HolomorphicAt (φ <| g ·) v₀ := (.imp (hg.continuousAt ·) (·.comp hg) ∘ @h · · ·)

/-- A family φ of complex points holomorphic at w₀ has a first-order jet τ at w₀ read through ℓ,
for every ℂ-linear map ℓ from the continuous dual of the parameter space P to M. -/
lemma HolomorphicAt.exists_isJet (h : HolomorphicAt φ w₀) ℓ : ∃ τ, IsJet (M := M) φ w₀ ℓ τ :=
  have H {U} a s := @h U _ (isRegularOn_ofSection s) (landsIn_iff_mem.2 a)
  have C {f g} (e : f =ᶠ[𝓝 w₀] g) := congr(inl $e.eq_of_nhds + inr (ℓ $e.fderiv_eq.1))
  let j {U} (a : _ ∈ U) : Γ(X, U) →+* _ := by
    use! fun s ↦ inl (PointFn.ofSection s _ (φ w₀)) + inr (ℓ (fderiv ℂ (PointFn.ofSection s _ <|
      φ ·) w₀)) <;> simp [C ((H a 0).1.mono fun _ ↦ (ofSection_eq · 1 ▸ map_one _)), fderiv_fun_add,
      (H a _).2.differentiableAt]
  ⟨map (colimit.desc _ ⟨_, by use (ofHom <| j ·.1.2), fun _ V _ ↦ by ext; exact C ((H V.1.2
    0).1.mono fun _ ↦ ofSection_map _ _)⟩) ≫ X.fromSpecStalk _, fun _ _ b ↦ have a :=
      (landsIn_fromSpecStalk (landsIn_iff_mem.1 b)); ⟨a.comp _, by erw [isRegularOn_ofSection,
      ofSection_fromSpecStalk, colimit.ι_desc_apply] <;> tauto⟩⟩

lemma isJet_comp_iff (hg : HasFDerivAt (𝕜 := ℂ) g g' v₀) (h : HolomorphicAt φ (g v₀)) :
  IsJet (φ <| g ·) v₀ (.applyₗ v) τ ↔ IsJet φ (g v₀) (.applyₗ (g' v)) τ := forall₃_congr fun _ _ ↦
  (h (isRegularOn_ofSection _) · |>.2.differentiableAt.hasFDerivAt.comp _ hg |>.fderiv ▸ .rfl)

lemma isFirstOrderConst_iff : IsFirstOrderConst φ w₀ v ↔ ∀ U s, LandsIn (φ w₀) U →
  fderiv ℂ (@PointFn.ofSection X U s _ <| φ ·) w₀ v = 0 := by simp_all [isRegularOn_ofSection _ _]

attribute [local simp ←] map_comp_assoc ofHom_comp

lemma Uniformisation.immersive_of_isPullback {p c} (H : IsPullback p A.hom s c) z :
  IsHolImmersionAt (atGeneric u.expMap · ≫ p) z :=
  (u.immersive z).imp (·.comp_hom p) fun i v k ↦ have ⟨_, h⟩ := (u.immersive z).1.exists_isJet _
  i v ((H.hom_ext ((h.comp_hom p).unique k :) (by simp [h.comp_base_eq])).subst h)

/-- Let 𝒜 be a commutative group scheme over X, smooth of relative dimension d, φ a family of
complex points of 𝒜 holomorphic at w₀, and n ≠ 0. If nφ is constant to first order in the
direction v, so is φ. -/
lemma HolomorphicAt.isFirstOrderConst_of_nsmul {𝒜 : Over X} [AddObj 𝒜] {φ d n} (h :
  HolomorphicAt φ w₀) (hd : SmoothOfRelativeDimension d 𝒜.hom) (hn : n ≠ 0) (k : IsFirstOrderConst
  (φ · ≫ (n • 𝟙 𝒜).left) w₀ v) : IsFirstOrderConst φ w₀ v := (h.exists_isJet _).elim fun τ t ↦
  (by simpa using! (congr($(sub_eq_zero.1 ((IsInfinitesimal.nsmul_injective_and_eq_zero (y :=
  homMk _ ((t.comp_hom _).unique (by simpa using k.comp_hom 𝒜.hom)) ≫ 𝟙 _ - homMk _ ≫ 𝟙 _)
  (by erw [IsInfinitesimal, AddGrpObj.comp_sub, sub_eq_zero]; ext; exact t.fst_comp.trans (by simp))
  hd (𝟙 _) n).1 (by simpa [isUnit_iff_isUnit_fst]) (by
            simp_rw [smul_sub, sub_eq_zero, ← comp_nsmul]
            ext; exact (t.comp_hom _).unique k))).1)) : τ = _).subst t

/-- Let O act on A = V/L by linear F_a on V and by matrices m_a in dim V coordinates at 0. Some
ρ-eigenline of m contains the image of m_b − ρ(c) iff some ρ-eigenline of F contains that of
F_b − ρ(c). -/
lemma Uniformisation.hasSignature_iff {O g} [CommRing O] [ModuleObj O A] {F : O → V →L[ℂ] V} (hF :
  ∀ a w, u.expMap (F a w) = a • u.expMap w) {𝒜} [AddObj 𝒜] [ModuleObj O 𝒜] {s U z m p} (J :
  IsLieChart (ι := Fin g) 𝒜 s U z m) (h : @IsGroupBaseChange S
  _ s 𝒜 _ O _ _ A _ _ p) (hd : Module.finrank ℂ V = g) {ρ b c} : HasSignature ρ b c m ↔ ∃ Y ≠ 0,
  (∀ a, F a Y = ρ a • Y) ∧ ∃ ξ : V →ₗ[ℂ] ℂ, ∀ w, F b w - ρ c • w = ξ w • Y := by
  choose τ k using ((u.immersive 0).1.exists_isJet <| .applyₗ ·)
  let τ v : specOver .. ⟶ A := homMk _ (by simpa using (k v).comp_base_eq (u.expMap · |>.w))
  have Z := by simpa [↓map_zero] using h.pullSection_comp 0
  have N v : IsInfinitesimal _ (h.pointEquiv (τ v)) :=
    OverMorphism.ext (((k v).fst_comp =≫ _).trans (by simp [Z]))
  let D := LinearMap.pi fun j ↦ (fderiv ℂ (PointFn.ofSection (z j) _ <|
    atGeneric u.expMap · ≫ p.1) 0).1
  have d v : tangentCoords z (h.pointEquiv (τ v)) =
    inr ∘ D v := by simp [isRegularOn_ofSection _ _, tangentCoords, τ, Z, D, (k v).comp_hom _ U,
    IsGroupBaseChange.pointEquiv, by simpa using (J.2 (map_id _ =≫ s)).1]
  let D := D.linearEquivOfInjective (.of_ker _ fun v _ ↦
    (u.immersive_of_isPullback h.1 0).2 v ((congr($(J.1.eq_zero_of_tangentCoords
    (J.2 rfl).1 (N v) (by simp [*])).1).trans (by simp [Z])).subst ((k v).comp_hom _))) (by simpa)
  have M a v : D (F a v) = m a *ᵥ D v := by simpa [d, mulVec_eq_sum, snd_sum, ← map_smul,
    ← (by ext; exact ((isJet_comp_iff (by fun_prop) (u.immersive _).1).2 ((F a).map_zero ▸
    k _)).unique (by simpa [hF, ← comp_left] using (k v).comp_hom (τ := (τ v).1) (a • 𝟙 A).1) :
    τ (F a v) = a • τ v)] using! congr(snd ∘ $(((J.2 rfl).2 (N v)).1 a))
  simp [HasSignature, ↓reindex_equiv D.symm, ← D.apply_eq_iff_eq, M, ext_iff_mulVec,
    reindex_equiv (D.symm.dualMap ≪≫ₗ (dotProductEquiv ..).symm).symm, vecMulVec_mulVec]
