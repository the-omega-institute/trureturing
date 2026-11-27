/- GID: D5/S3/Zeros/GRH/Lib/Shimura/AbelianScheme/ThetaFamily
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/AbelianScheme/ThetaFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.AbelianScheme.ThetaFamily. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/AbelianScheme/ThetaFamily.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation.PeriodLattice
import D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation.UniformisationExists
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Abelian schemes (isogenies finite flat, [m]*L = L^{m²}, Cartier, unramified
torsion). Here abelian scheme means smooth, proper and divisible, over any local ring. The
parallelogram law is a hypothesis in place of the theorem of the cube, and quasi-finiteness is read
from a projective embedding. Source: B. Edixhoven, G. van der Geer, B. Moonen, Abelian Varieties
(draft), (5.1)–(5.2) and ch. IV §3; The Stacks project, Section 0BF9; EGA IV and S. Bosch, W.
Lütkebohmert, M. Raynaud, Néron Models (1990) 7.3, 8.1.

Part of: Moduli of abelian varieties by theta values (theta-null embedding, universal family) (known
result; see Lib.Shimura.ThetaModuli.UniversalFamily).

This file: Isogenies are finite flat; homomorphisms killing the kernel factor through them.
Uniqueness of linear lifts, lattice index as determinant norm, number of torsion points.
Theta-embedded PEL families, their objects, pull-backs, full level structures, logarithm along a
line. -/

noncomputable section

section

open CategoryTheory Category AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
  Algebra TensorProduct HasRingHomProperty MorphismProperty RingHom Module Flat LinearMap
  IsLocalRing Over CommRingCat Ideal Scheme Spec IsLocalization AtPrime AddMonObj

/-- Over Artinian k, let A be a commutative group scheme, B, C abelian schemes, f : A → B a
finite flat surjective homomorphism. A homomorphism g : A → C killing the points of ker f in
finite local k-algebras factors through f by a homomorphism. -/
lemma exists_factor_through_isogeny {k} [CommRing k] [IsArtinianRing k] {A B C} [AddObj A]
  [IsAbelianScheme B] [IsAbelianScheme C] (f : A ⟶ B) [F : IsIsogeny f] (g : A ⟶ C) [IsAdditive g]
  (h : ∀ S [CommRing S] [IsLocalRing S] [Algebra k S] [Module.Finite k S] [IsNoetherianRing S] (y :
  specOver k S ⟶ _), y ≫ f = 0 → y ≫ g = 0) : ∃ j, IsAdditive j ∧ f ≫ j = g := by
  choose S ι _ _ _ o H using exists_finite_kernel_ring F.2
  choose I _ r using exists_ideal_le_ker_iff_factors ζ[C].1 (ι ≫ g).1
  have : ι ≫ g = 0 := by
    simpa [eq_zero_iff_factors_zero_section] using (r (.id _)).1 (eq_zero_of_localization ·
      fun J _ ↦ (r _).2 (eq_zero_iff_factors_zero_section.1 (@h _ _ _ _ .of_quasiFinite
      (EssFiniteType.isNoetherianRing k _) (specOver.map ⟨_, by tauto⟩ ≫ ι) (by simp [o]))) ·)
  peel exists_hom_of_rel g _ (by bound) (by simp) (H · · |>.elim (by aesop))
    (.singleton f.1) (by simp) fun _ _ ⟨⟩ ↦ ⟨homMk (𝟙 _), rfl⟩
  simp [this _ (𝟙 _)]

/-- A locally quasi-finite surjective homomorphism of abelian schemes over a local ring is an
isogeny: it is finite and flat (and surjective).

Known result: Abelian schemes: isogenies finite flat, [m]*L = L^{m²}, Cartier, unramified
torsion. -/
lemma finite_flat_of_quasiFinite {R} [CommRing R] [IsLocalRing R] {A B}
  [@IsAbelianScheme (Spec ⟨R⟩) A] [IsAbelianScheme B] (f : A ⟶ B) [IsAdditive f] (h :
  LocallyQuasiFinite f.left) (hf : Surjective f.left) : IsIsogeny f := by
  have G {T Y P} [IsMultiplicative P] [P.IsStableUnderBaseChange] {x : T ⟶ B} y (_ : P x.left) (_ :
    P Y.hom) : P (fst .. ≫ x + snd T Y ≫ y).left := let τ s := lift (fst B Y + snd .. ≫ s) (snd ..)
    have : IsIso (τ y) := ⟨τ (-y), by aesop⟩
    by simpa [τ] using show P (x ▷ Y ≫ τ y ≫ fst ..).1 by apply_rules [pullback_fst,
      overPullbackMap, RespectsIso.precomp, comp_mem]
  have ⟨L, i, _, ⟨y, _⟩, hx⟩ := exists_Spec_apply_eq (ζ[B].1 (closedPoint R))
  obtain ⟨⟨τ, v⟩, _⟩ := map_surjective (i ≫ B.3), IsFinite.of_isProper_of_locallyQuasiFinite f.1
  algebraize [τ.1]
  have ⟨q, a@⟨⟨_, _⟩, _⟩, _⟩ := exists_minimalPrimes_le (map_le_of_le_comap
    congr($(congr($v _).trans (congr(B.3 $hx).trans congr($(ζ[B].w) _))).1).ge)
  let D := Localization.AtPrime q
  have E := radical_map_of_mem_minimalPrimes D _ _ a
  erw [← map_radical q.primeCompl, ((isRadical_iff_quotient_reduced _).2 (@isReduced_of_injective
    _ _ _ _ _ _ _ _ (@quotIdealMapEquivQuotTensor R ..).injective ((affine_isReduced_iff _).1 ((v ▸
    inferInstance : GeometricallyReduced (map τ)).1 _ _ _ ((isPushout_tensorProduct _ (ResidueField
    R) _).op.map Scheme.Spec))))).radical, Ideal.map_map, map_eq_maximalIdeal q D] at E
  have ⟨u, fu⟩ : ∃ u : specOver R D ⟶ B, Flat u.1 := ⟨homMk _ (v ▸ map_comp τ _).symm,
    (SpecMap_iff.2 (flat_algebraMap_iff.2 inferInstance)).comp ..⟩
  obtain ⟨⟨P, φ, j, H⟩, hq⟩ := exists_isPullback_SpecMap f.1 u.1,
    IsPullback.of_hasPullback f (snd A _ ≫ u)
  algebraize [φ.1, φ.1.comp (algebraMap R D)]
  refine .mk (toFlat := (descendsAlong_flat (.mk _ respectsIso (by simp_all [flat_algebraMap_iff,
    faithfullyFlat_algebraMap_iff, iff_flat_tensorProduct]))).1 ((.mk' (by simp [hq.w]) (by simp_all
    [pullback.hom_ext_iff, ← assoc]) fun _ c b e ↦ ⟨hq.lift (b - c ≫ fst ..) c (by simp [← e]), by
    simp⟩ : IsPullback _ (pullback.snd .. ≫ fst .. + pullback.fst ..) (_ + _) f).map (Over.forget
    _)) ⟨⟨G u hf ((flat_and_surjective_SpecMap_iff _).2 (@.of_flat_of_isLocalHom _ _ _ _ (_)
    _ _ (by simpa using! fu.comp _ B.3) (((local_hom_TFAE _).out 3 1).1 E.le))).2, by
    simpa [add_comm, ↓← comp_left] using comp (β_ A _).1.1 _ (hg := G f fu inferInstance)⟩,
    by simpa using .of_comp _ B.hom⟩ (of_isPullback ((hq.map _).of_right' H) (Spec_iff.2 ?_)))
  apply_rules +allowSynthFailures [of_free, free_of_maximalIdeal_rTensor_injective,
    locallyOfFinitePresentation_left, FinitePresentation.of_finite_of_finitePresentation,
    (IsFinite.SpecMap_iff _).1, of_isPullback, (LocallyOfFinitePresentation.SpecMap_iff _).1]
  rw [← lTensor_inj_iff_rTensor_inj, ← show (liftBaseChange D
    ((Algebra.linearMap R D).domRestrict _)).range = maximalIdeal D by simpa]
  refine .of_comp_right (.of_comp (f := TensorProduct.rid ..) ?_) ((lTensor_surjective _ (
    surjective_rangeRestrict _)).comp (AlgebraTensorModule.cancelBaseChange _ _ P ..).3.surjective)
  convert (TensorProduct.rid ..).injective.comp (iff_lTensor_injective'.1 (by
    simpa [(of_isPullback H.flip fu).comp .., ← Spec.map_comp] using! congr(Flat $(H.w =≫ B.3))) _)
  ext x; induction x <;> simp_all

end

section

open Int Complex AddSubgroup LinearMap ComplexConjugate CategoryTheory MonoidalCategory Module
variable {O} [CommRing O] [ValuativeArc O] {A} [AddObj A] {V V'} [FinComplexSpace V]
  [FinComplexSpace V'] (u : Uniformisation (O := O) A V)

lemma Uniformisation.linear_ext {F G : V' →L[ℂ] _} (h : ∀ z, u.expMap (F z) = u.expMap (G z)) : F =
  G := F.ext (by simpa using
  TotallyDisconnectedSpace.eq_of_continuous (β := u.L) _ ((F - G).2.subtype_mk (by simp [*])) · 0)

/-- Let L be a lattice in a finite-dimensional complex space V and F an injective ℂ-linear
endomorphism of V with F(L) ⊂ L. Then the index of L in F⁻¹(L) equals det F times its
complex conjugate, that is |det F|². -/
lemma relIndex_comap_lattice {L} [IsFullRankLattice L] {F : V →ₗ[ℂ] V} (h : ∀ z ∈ L, F z ∈ L) (hb :
  (⇑F).Injective) :
  relIndex L.toAddSubgroup (L.toAddSubgroup.comap F) = F.det * conj F.det := let b := finBasis ℤ L
  by erw [relIndex_eq_natAbs_det _ _ h b (b.map (.symm (.ofSubmodule' (.restrictScalars _
      (.ofInjectiveEndo _ hb)) _))), mul_conj, ← abs_of_nonneg (normSq_nonneg _), Nat.cast_natAbs,
      ← Algebra.norm_complex_apply, ← det_restrictScalars, ← det_toMatrix (b.ofZLatticeBasis ℝ),
      ofReal_inj, cast_abs, cast_det]
     rcongr; simpa [toMatrix_apply] using! (b.ofZLatticeBasis_repr_apply ..).symm

/-- Let O be a valuation ring with fraction field ℂ, A a commutative group scheme over O, and
V/L ≅ A(O) a uniformisation with dim V = d. For m ≠ 0, exactly m^{2d} points of A(O) are
killed by m. -/
lemma Uniformisation.card_torsion (u : Uniformisation A V) {m} (hm : m ≠ 0) :
    .card {y : 𝟙_ _ ⟶ A // m • y = 0} = m ^ (finrank ℂ V * 2) := by
  erw [← congr(Nat.card $((nsmulAddMonoidHom m).ker.map_comap_eq_self_of_surjective u.4)),
    ← relIndex_ker, ← @Nat.cast_inj ℂ]
  convert! @relIndex_comap_lattice _ _ u.L _ ((m : ℂ) • 1) _ (lsmul_injective ?_)
    <;> simp_all [SetLike.ext_iff, pow_mul, sq, Nat.cast_smul_eq_nsmul, ↓det_smul]

end

open CategoryTheory AlgebraicGeometry MonoidalCategory NumberField Over LineBundle OverMorphism
  Matrix Spec Pic
variable {E} [Field E] [CMBase E] (D : PEL E)

/-- A family for the PEL data D: an abelian scheme with O_E-action over an O_E-scheme S, of
relative dimension n[E⁺:ℚ], embedded by theta coordinates, with level points and signature
condition, whose theta data determine affine points of S. -/
structure ThetaFamily S (τ : S ⟶ Spec ⟨𝓞 E⟩) where
  A : Over S
  [isAbelianScheme : IsAbelianScheme A]
  [moduleObj : ModuleObj (𝓞 E) A]
  N : LineBundle ..
  embeds : N.IsProjEmbedding A.hom
  η : D.levelTorsion →ₗ[𝓞 E] 𝟙_ _ ⟶ A
  theta_law {B} [CommRing B] [IsLocalRing B] (t : Spec ⟨B⟩ ⟶ S) {T} [AddObj T] [ModuleObj _ T] {q}
    (h : IsGroupBaseChange t (B := T) q) : ∃ c, IsThetaStructure (D.lagrangian.addSubgroupOf _)
      (.comp (h.pullSection ∘ₗ η) (AddSubgroup.inclusion D.T_le_levelTorsion)) (embeds.1.pull
    q.left) c
  class_laws : D.HasClassLaws N.picClass
  signature (b : ℤ) {B} (t : Spec B ⟶ S) [IsLocalRing B] : ∃ V z m, IsLieChart A (ι := Fin
    (abelianDim E D.Index)) t V z m ∧ HasSignature (preimage (t ≫ τ)).hom (star D.β - b) (D.β - b) m
  relative_dim : SmoothOfRelativeDimension (abelianDim E D.Index) A.hom
  eq_of_list_eq {B} (t t' : Spec B ⟶ S) : t ≫ τ = t' ≫ τ →
    (∀ l, N.pull (t ≫ (η l).left) = N.pull (t' ≫ (η l).left)) → t = t'

attribute [instance] ThetaFamily.moduleObj ThetaFamily.isAbelianScheme ThetaFamily.relative_dim

variable {D} {S S' Z : Scheme} (b : S' ⟶ S) {τ} {X : ThetaFamily D Z τ} {R K} [CommRing R]

/-- An object of the family X over a scheme T: a morphism from T to the base of X. -/
abbrev ThetaObject (_ : ThetaFamily D Z τ) T := T ⟶ Z

variable (x : ThetaObject X S) (y : ThetaObject X (Spec ⟨R⟩))

namespace ThetaObject

/-- The group scheme with O_E-action of an object x over S: the pull-back of the abelian scheme
of the family along x : S → base. -/
def groupScheme := X.A.pullback x deriving AddObj, ModuleObj (𝓞 E), IsAbelianScheme

/-- The projection from the abelian scheme of an object x to that of the family X, as a morphism
over the base of X. -/
def toFamily : map x x.groupScheme ⟶ X.A := (mapPullbackAdj _).counit _

lemma isGroupBaseChange : IsGroupBaseChange _ x.toFamily := isGroupBaseChange_counit _

instance smoothOfRelativeDimension : SmoothOfRelativeDimension (abelianDim E D.Index)
  x.groupScheme.hom := by simp [groupScheme]; infer_instance

attribute [irreducible] groupScheme toFamily

/-- The line bundle, with its coordinates, on the abelian scheme of an object: the pull-back of
the bundle N of the family along the projection. -/
def lineBundle := @pull _ x.groupScheme.left _ X.N x.toFamily.left

lemma isProjEmbedding : x.lineBundle.IsProjEmbedding x.groupScheme.hom :=
  X.embeds.of_isPullback x.isGroupBaseChange.1

/-- The level points of an object: the O_E-linear map from the 𝔑-torsion of (𝔸_f / Ô)ⁿ to
sections of its abelian scheme, pulled back from those of the family. -/
def levelPoints := x.isGroupBaseChange.pullSection ∘ₗ X.η

lemma levelPoints_comp_toFamily l : (x.levelPoints l).left ≫ x.toFamily.left = x ≫ (X.η l).left :=
  x.isGroupBaseChange.pullSection_comp _

lemma hasClassLaws :
  D.HasClassLaws x.lineBundle.picClass := by apply X.class_laws.imp <;> simp [ParallelogramLaw,
  pairing, lineBundle, x.isGroupBaseChange.atPoint_picClass_pull] <;> solve_by_elim

/-- For an object x, an integer b, a natural number k and scheme-valued points y, z of its abelian
scheme, ⟨(β − b)^k y, z⟩ = ⟨y, (β̄ − b)^k z⟩ for the pairing of [N]. -/
lemma pairing_pow_smul_adjoint (b : ℤ) k {T} : ∀ y z : T ⟶ _,
  x.lineBundle.picClass.pairing ((D.β - b) ^ k • y) z =
  x.lineBundle.picClass.pairing y ((star D.β - b) ^ k • z) := k.rec (by simp) fun k h y z ↦ by
  rw [pow_succ, mul_smul, h, pow_succ', mul_smul]
  generalize b = b, (_ : 𝓞 E) • z = z
  induction b using
    Polynomial.Chebyshev.induct <;> simp_all [D.star_beta, sub_smul, add_smul, two_smul,
    ← sub_sub, ← sub_add, x.hasClassLaws.2] <;> grind [x.hasClassLaws.1.pairing_add_add_pairing_sub,
    sub_add_cancel, pairing_comm, neg_sub, x.hasClassLaws.2 z y, sub_smul, one_smul, by
    simpa [pairing.eq_1 _ 0] using x.hasClassLaws.1.pairing_add_add_pairing_sub (y - y)]

/-- The object x' over S' is the pull-back of the object x over S along b : S' → S: as maps to
the base of the family, x' = x∘b. -/
abbrev IsPullbackAlong (x' x : ThetaObject X _) := b ≫ x = x'

namespace IsPullbackAlong

variable {b x x'} (h : IsPullbackAlong b x' x)

/-- For x' the pull-back of x along b, the S-morphism from the abelian scheme of x' to that of x
that commutes with the projections to the family. -/
def schemeMap : map b x'.groupScheme ⟶ x.groupScheme :=
  x.isGroupBaseChange.pointEquiv.symm (homMk x'.toFamily.left (by simp [h]))

lemma comp_toFamily : h.schemeMap.left ≫ x.toFamily.left = x'.toFamily.left :=
  x.isGroupBaseChange.1.lift_fst ..

/-- If x' is the pull-back of x along b : S' → S, then `ThetaObject.IsPullbackAlong.schemeMap` makes
the abelian scheme of x' the base change along b of that of x, O_E-linearly on points. -/
lemma isGroupBaseChange : IsGroupBaseChange b h.schemeMap := by
  obtain ⟨P, rfl⟩ := x'.isGroupBaseChange, id h
  use .of_right (h.comp_toFamily ▸ P.1) h.schemeMap.w x.isGroupBaseChange.1, fun {T} ↦ ?_
  convert (P.pointEquiv ≪≫ₗ x.isGroupBaseChange.pointEquiv (T := T.map b).symm).isLinear
  apply x.isGroupBaseChange.pointEquiv.eq_symm_apply.2 (ext (_ ≫= h.comp_toFamily))

lemma lineBundle_eq_pull : x'.lineBundle = x.lineBundle.pull h.schemeMap.left :=
  congrArg _ h.comp_toFamily.symm

lemma lineBundle_pow_eq_pull m : x'.lineBundle.pow m = (x.lineBundle.pow m).pull h.schemeMap.left :=
  h.lineBundle_eq_pull ▸ (pull_pi _).symm

lemma levelPoints_eq_pullSection l : x'.levelPoints l = h.isGroupBaseChange.pullSection
  (x.levelPoints l) := ext (x'.isGroupBaseChange.1.hom_ext (by simp [↓levelPoints_comp_toFamily,
  ← h, ← h.comp_toFamily, h.isGroupBaseChange.pullSection_comp_assoc]) (by simp))

end IsPullbackAlong

lemma exists_isPullbackAlong : ∃ x', IsPullbackAlong b x' x := ⟨_, rfl⟩

/-- For an object x over Spec R, the ring homomorphism O_E → R induced by x and the structure
morphism of the base of the family to Spec O_E. -/
def baseHom : 𝓞 E →+* R := (preimage (y ≫ τ)).hom

/-- A full structure: an O_E-linear injection of (𝔸_f / Ô)ⁿ into sections extending the level
points; for each ι : R → ℂ and some unit ε of Ẑ, lifts of m-torsion translations to N^m
commute on coordinates up to c with ι(c) = ψ_f(εm·form). -/
structure FullStructure where
  torsionPoint : _root_.AdelicTorsion E D.Index →ₗ[𝓞 E] 𝟙_ _ ⟶ y.groupScheme
  injective : (⇑torsionPoint).Injective
  eta_eq l : y.levelPoints l = torsionPoint l
  weil_pairing (ι : R →+* ℂ) : ∃ ε : (Ô ℚ)ˣ, ∀ (m : ℕ) x z, m • torsionClass x = 0 →
    m • torsionClass z = 0 → ∃ c, ι c = ψf E (finAdeleIncl ℚ E ε * (m * xiForm D.ξ x z)) ∧ ∀ Φ Ψ,
    IsTranslationLift (y.lineBundle.pow m) (torsionPoint (torsionClass x)) Φ → IsTranslationLift _
    (torsionPoint (torsionClass z)) Ψ → ∀ h i, Φ (Ψ (coordSection h i)) =
    c • Ψ (Φ (coordSection h i))

lemma IsPullbackAlong.baseHom_eq_comp [CommRing K] {φ : R →+* K} {x y : ThetaObject X _} (e :
  y.IsPullbackAlong (specMap φ) x) :
  y.baseHom = φ.comp x.baseHom := by simp [ThetaObject.baseHom, ← e]

variable [IsLocalRing R] {φ : R →+* ℂ} {y y'} (h : IsPullbackAlong (specMap φ) y' y)

/-- For an object over a local ring with ρ(β) = b ∈ ℤ, some ω sends points x of A vanishing
modulo a square-zero ideal into that ideal, additively, compatibly with base change, with
ω(cx) = ρ(c)ω(x); and ω(x) = 0 forces (β̄ − b)x = 0. -/
lemma exists_tangent_log {b : ℤ} (hb : y.baseHom (D.β - b) = 0) : ∃ ω : ∀ ⦃C⦄ ⦃_ : Spec C ⟶ _⦄,
  (_ ⟶ y.groupScheme) → C, ∀ ⦃C C' ψ⦄ [@IsSqZeroExt C C' ψ] ⦃t⦄ ⦃x : .mk t ⟶ y.groupScheme⦄,
  IsInfinitesimal ψ x → (∀ c, ω (c • x) = preimage t (y.baseHom c) * ω x) ∧
  (ω x = 0 → (star D.β - b) • x = 0) ∧ (∀ ⦃x'⦄, IsInfinitesimal ψ x' → ω (x + x') =
  ω x + ω x') ∧ ψ (ω x) = 0 ∧ ∀ ⦃D χ t'⦄ (a : .mk (t' : Spec D ⟶ _) ⟶ Over.mk t), a.left = Spec.map
  χ → ω (a ≫ x) = χ (ω x) := let ⟨V, z, m, ⟨J, M⟩, Y, ξ, k, E⟩ := X.signature b y
  ⟨fun _ _ x ↦ tangentCoords z ((star D.β - b) • y.isGroupBaseChange.pointEquiv x) k,
    fun _ _ ψ _ t x h ↦ by
  have T {x} : IsInfinitesimal .. → IsInfinitesimal ψ (y.isGroupBaseChange.pointEquiv (T :=
    .mk t) x) := y.isGroupBaseChange.pointEquiv.map_eq_zero_iff.2
  obtain ⟨⟨i, M⟩, N⟩ := M (map_preimage t =≫ _), (T h).smul _
  exact ⟨(by simp_all [smul_comm _ ·, M N, M (T h), baseHom, ← Matrix.map_mul, mul_vecMulVec,
    map_smul']), fun _ ↦ y.isGroupBaseChange.pointEquiv.injective
    (by simp_all [J.eq_zero_of_tangentCoords i N, M (T h), baseHom,
    (E.1.map _).mul_right_eq_zero, funext_iff, mulVec_apply_eq_sum, mul_assoc, vecMulVec,
    ← Finset.mul_sum]), fun _ h ↦ by simp [M N, (T h).smul], J.map_tangentCoords_eq_zero i N k,
    fun _ _ _ a e ↦ by simpa using! congrFun (J.tangentCoords_comp i N ((map y).2 a) e) k⟩⟩

lemma FullStructure.exists_isTranslationLift (e : y.FullStructure) {m l} (a : m • l = 0) : ∃ Φ,
  IsTranslationLift (y.lineBundle.pow m) (e.torsionPoint l) Φ := by
  simp [exists_isTranslationLift_iff, y.hasClassLaws.1.nsmul_class_pairing, ← comp_nsmul,
    ← map_nsmul, a, pairing.eq_1]

/-- Let R be a local ring, φ : R → ℂ a local homomorphism and y' the pull-back of the object y
along φ. For every full structure on y, pulling back its sections gives a full structure on
y'. -/
lemma FullStructure.exists_pullback [IsLocalHom φ] (e : y.FullStructure) : ∃ e' : y'.FullStructure,
  e'.torsionPoint = h.isGroupBaseChange.pullSection ∘ₗ e.torsionPoint :=
  ⟨⟨_, .of_ker _ fun x k ↦ (exists_nsmul_adelicTorsion_eq_zero x).elim fun m _ ↦ e.injective (by
  simp [section_eq_zero_of_torsion y.smoothOfRelativeDimension (.of_map φ ↑m (by aesop))
    (by simp_all [← map_nsmul]) (h.isGroupBaseChange.pointEquiv.symm.map_eq_zero_iff.1 k)]), by
  simp [h.levelPoints_eq_pullSection, e.eta_eq], fun ι ↦ by
  peel e.weil_pairing (ι.comp φ) with _ m x z a b H
  obtain ⟨⟨_, c'⟩, ⟨_, d'⟩, P, L : IsLinearSystem (pow _ m), _, g, H⟩ :=
    e.exists_isTranslationLift a, e.exists_isTranslationLift b, isSectionLift_pullSections _
    h.schemeMap.w (h.lineBundle_pow_eq_pull m), .pi fun _ ↦ y.isProjEmbedding.1, H
  refine ⟨_, g, fun Φ Ψ c d l i ↦ ?_⟩
  have U {z Φ Ψ} c c' := (h.isGroupBaseChange.translation_comp z ▸ IsSectionLift.comp (Θ :=
    Φ) c P).exists_eq_smul (hasConstFunctions_of_isPullback .of_id_fst) (P.comp (Φ := Ψ) c')
  obtain ⟨⟨⟩, ⟨⟩⟩ := U c c', U d d'; simp_all
    [← pullSections_coordSection L _ h.schemeMap.w (h.lineBundle_pow_eq_pull m)]; module⟩, rfl⟩
