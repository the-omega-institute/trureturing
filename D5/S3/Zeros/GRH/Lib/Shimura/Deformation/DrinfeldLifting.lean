/- GID: D5/S3/Zeros/GRH/Lib/Shimura/Deformation/DrinfeldLifting
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/Deformation/DrinfeldLifting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.Deformation.DrinfeldLifting. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/Deformation/DrinfeldLifting.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.CongruenceRelation.KernelReduction
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Deformations of the PEL object have at most n-1 parameters (known result; see
Lib.Shimura.Deformation.TangentBound).

This file: Linear functions on w-torsion with zero differential span at most n-1 dimensions.
Absolute Frobenius of a scheme; pull-back of line bundles is a power. Drinfeld's lifting lemma for
first-order deformations of the abelian object. -/

open Algebra Polynomial AlgebraicGeometry CategoryTheory Fintype IsAlgClosed LinearMap minpoly
  specOver Module Submodule RingHom TrivSqZeroExt Ideal Quotient FiniteField IsLocalRing
  CartesianMonoidalCategory CommRingCat LineBundle Spec
variable {E} [Field E] [CMBase E] {D : PEL E} {k} [Field k] [IsAlgClosed k] {Z σ} {Y :
  ThetaFamily D Z σ} {x : ThetaObject Y (Spec ⟨k⟩)}

open Fint in /-- If `x ↦ x ^ i` is `F`-linear on an algebraically closed extension of a field `F`
with `q` elements, then `i` is a power of `q`: the fixed points of
`x ^ (q i)` form an `F`-space. -/

lemma mem_powers_card_of_isLinearMap_pow F {i} [Field F] [Finite F] [Algebra F k]
    (h : IsLinearMap F (· ^ i : k → k)) : i ∈ Submonoid.powers (.card F) :=
  have s := galois_poly_separable _ (Fintype.card F * i) (ringChar.dvd (by simp))
  have e := ((card_rootSet_eq_natDegree s (splits _)).trans (X_pow_card_sub_X_natDegree_eq F
    ((Nat.two_le_iff _).2 (by simpa [one_lt_card.ne'] using h.map_zero)))).symm.trans
    (@card_eq_pow_finrank F ((h.mk' ∘ₗ frobeniusAlgHom F k).fixedSubmodule.copy (rootSet _ k) (by
    simp [Set.ext_iff, mem_rootSet, s.ne_zero, ← pow_mul])) _ _ _ _ (_))
  ⟨_, by simpa using (mul_pow_sub_one (fun _ ↦ by simp_all [one_lt_card.ne']) _).trans e.symm⟩

attribute [local simp ←] torsionBySet_eq_torsionBySet_span

/-- For x reducing a full y at a good place w, let f be natural semilinear maps A_x[w](C) → Hom_k(W,
C), C local k-algebras, vanishing on tangent vectors at 0. If no nonzero l ∈ W is killed for all
finite C, then dim W ≤ n − 1. -/
lemma finrank_le_of_placeTorsion (hw : D.IsGoodAt (ker x.baseHom)) {V : ValuationSubring ℂ} {φ :
  V →+* k} {y} (hy : x.IsPullbackAlong (specMap φ) y) (e : y.FullStructure) {W} [AddCommGroup W]
  [Module k W] (f : ∀ C [CommRing C] [Algebra k C] [IsLocalRing C], placeTorsion x C →ₛₗ[x.baseHom]
  W →ₗ[k] C) (hf : ∀ {C C'} [CommRing C] [Algebra k C] [CommRing C'] [Algebra k C'] [IsLocalRing C]
  [IsLocalRing C'] φ y l, f C' (placeTorsionMap φ y) l = φ (f C y l)) (hf₂ : ∀ y, specOver.map
  (fstHom k k k) ≫ y.1 = 0 → f _ y = 0) (H : ∀ l, (∀ C [CommRing C] [Algebra k C] [IsLocalRing C]
  [Module.Finite k C] y, f C y l = 0) → l = 0) : finrank k W ≤ card D.Index - 1 := by
  obtain ⟨⟨-, ⟨h0, p, i, ⟨hp⟩⟩, _, ⟨g⟩⟩, ν, -, hτ⟩ := isGoodAt_ker_spec hw,
    exists_param_pow_card_eq_zero hw e hy
  obtain ⟨⟨c, hc'⟩, Z, hZ, hX, h₁, ⟨h₃⟩⟩ :=
    IsDedekindDomain.exists_eq_span_pair (mem_ker.2 i) hp, exists_lie_line x rfl g
  obtain ⟨Γ, ι₀, _, _, _, k₀, hι₀⟩ :=
    exists_finite_kernel_ring (@IsFinite.of_comp _ _ _ (lift (p • 𝟙 x.groupScheme) (c • 𝟙 _)).1 (fst
    _ x.groupScheme).1 (by simp [↓← Over.comp_left, (x.finite_flat_surjective_smul hp).2]) _)
  simp [CartesianMonoidalCategory.hom_ext_iff] at k₀ hι₀
  let v : placeTorsion .. := ⟨ι₀, by simp [placeTorsion, *]⟩
  have U C [CommRing C] [Algebra k C] : (placeTorsionMap (C' := C) · v).Bijective := ⟨fun _ _ h ↦
    map_bijective.1 ((Over.mono_of_mono_left ι₀).1 _ _ congr($h)), by simpa [placeTorsionMap,
    placeTorsion, *, map_bijective.2.exists, Function.Surjective] using @hι₀ (specOver k C)⟩
  obtain ⟨⟨o, ho⟩, _⟩ := (U k).2 0, Finite.of_surjective _ (U k).2, (ker_isPrime _).isMaximal h0
  let u := placeTorsionMap (algHom k Γ (Localization.AtPrime (comap o ⊥))) v
  have inj {C} [CommRing C] [Algebra k C] : (placeTorsionMap (C' := C) · u).Injective :=
    fun _ _ _ ↦ Localization.algHom_ext _ ((U _).1 (by simpa))
  have fac {C} [CommRing C] [Algebra k C] [IsLocalRing C] (π : C →ₐ[k] k) : ∀ y,
    placeTorsionMap π y = 0 → ∃ φ, placeTorsionMap φ u = y := (U _).2.forall.2 fun φ _ ↦
    ⟨IsLocalization.liftAlgHom fun g : primeCompl (comap o ⊥) ↦ (IsLocalHom.of_surjective π (⟨_,
    π.2 ·⟩)).1 _ (congr($(@(U _).1 (π.comp φ) _ (by simp [*])) g).trans_ne g.2).isUnit, by simp [u,
    ← placeTorsionMap_comp, (U _).1.eq_iff, AlgHom.ext_iff, algHom]⟩
  have N : placeTorsionMap _ ⟨Z 1, by simp +contextual [h₁]⟩ = 0 := Subtype.ext (hX 1)
  obtain ⟨s, hΔ⟩ := fac _ _ N
  have hs a := congr((placeTorsionMap _ $hΔ).1).trans (h₃ a)
  let z := (fstHom ..).comp s
  obtain ⟨τ, hτ₀, hN, K⟩ := hτ _ u z
  choose! γ hγ using fun i h ↦ (mulLeft k (τ ^ i)).range_dualMap_eq_dualAnnihilator_ker.ge
    ((mem_dualAnnihilator z).2 fun a e ↦ (ker_eq_maximalIdeal z (⟨_, z.2 ·⟩)).ge
    (h ∘ (·.mul_left_eq_zero.1 e)))
  simp [DFunLike.ext_iff, z, *] at hγ hτ₀ hN K
  have hdiv a (ha : (s a).fst = 0) := by simpa [z, *, eq_zero_iff_dvd] using (congr($(
    @inj _ _ _ (mkₐ k (span {τ})) (.comp (ofId ..) z) (by simp [z, *])) a))
  obtain ⟨m, -, hm⟩ := (dvd_prime_pow prime_X _).1 (dvd k τ (by simpa))
  let pb := PowerBasis.ofAdjoinEqTop (id ⟨_, monic_X_pow _, by simpa⟩) (by simpa [SetLike.ext_iff]
    using (antitone_nat_of_succ_le (f := (∀ s, τ ^ · * s ∈ k[τ])) (fun m h s ↦ (hdiv
    (s - z s • 1) (by simp [z])).rec fun d e ↦ eq_add_of_sub_eq e ▸ by simp [mul_add, h, pow_mem,
    ← mul_assoc, ← pow_succ, add_mem_cancel_left, k[τ].smul_mem]) bot_le fun _ ↦ by rw [hN]; simp))
  have hδ := by simpa [*] using K _ s ∘ ext hτ₀
  choose ρ hρ using fun a ↦ (⟨placeTorsionMap (pb.lift (a • τ) (hm.dvd'.rec (by simp +contextual
    [pb, _root_.smul_pow, by simpa [dvd_iff] using hm.dvd]))) u, by simpa [← placeTorsionMap_comp,
    ← hs, inj.eq_iff] using (pb.algHom_ext (by simp; ext <;> simp [pb, *]))⟩ : ∃ y,
    (placeTorsionMap s y).1 = Z a)
  let F := _ ⧸ ker x.baseHom
  let := Quotient.field (ker x.baseHom)
  algebraize [x.baseHom.kerLift]
  have lt {i} (h : τ ^ Nat.card F ^ i ≠ 0) : i < card D.Index - finrank F (placeTorsion x k) := by
    erw [lt_tsub_iff_right, ← pow_lt_pow_iff_right₀ (@Finite.one_lt_card F _ _), pow_add, ←
      natCard_eq_pow_finrank, ← card_torsionBySet_adelicTorsion h0, ← ν.ker.card_mul_index]
    simpa [AddSubgroup.index_ker, ν.range_eq_top.2 (hτ k · (.id ..) |>.rec (by simp +contextual
      [placeTorsionMap, Nat.card_ne_zero]))] using h ∘ (pow_eq_zero_of_le · hN)
  have := @lt 0 (hδ ∘ by simp +contextual)
  refine (((⟨_, Quot.ind (f k).2⟩ : _ →ₗ[F] _).flip.prod (.pi fun j : Set.Ioi (Fin.mk 0 this) ↦
    γ (Nat.card F ^ j.1.1) ∘ₗ f _ u)).finrank_le_finrank_of_injective (.of_ker _
    fun l h₀ ↦ H l fun C _ _ _ _ x ↦ ?_)).trans (by simp [finrank_linearMap, -card_fin]; omega)
  have h₁ : f _ u l = 0 := zero_dvd_iff.1 (hN ▸ (Nat.card _).rec (by simp) fun i ⟨g, h⟩ ↦ (em (τ ^ i
    = 0)).rec (by simp [h, ·]) fun hi ↦ h ▸ mul_dvd_mul_left _ (hdiv _ (by_contra fun hg ↦ by
    have key {y a} (hy : (placeTorsionMap s y).1 = Z a) : a ^ i = γ i (f _ y l) / (s g).fst := by
      obtain ⟨φ, rfl⟩ := fac z y ((placeTorsionMap_comp ..).trans (Subtype.ext (hy ▸ hX a :)))
      simp [← placeTorsionMap_comp, inj.eq_iff, ← hs, AlgHom.ext_iff] at hy
      cases hdiv (φ τ) (by simp [*])
      simp [*, mul_pow, mul_assoc, by simpa [*, mul_comm] using congr($(hy τ).snd)]
    obtain ⟨j, rfl⟩ := mem_powers_card_of_isLinearMap_pow F ⟨fun a b ↦ (@key (ρ a +
      ρ b) _ (by simp [*])).trans (by simp [key (hρ _), add_div]), Quot.ind fun a b ↦ by
      simpa [key (hρ _), ← mul_div] using! @key (a • ρ b) _ (by simp [*]; rfl)⟩
    simpa [h, hγ, hi, hg] using congr($h₀.2 ⟨⟨_, lt hi⟩, j.pos_of_ne_zero (by
      simpa [·, *] using congrArg snd (hf s u l))⟩))))
  let π := lift.comp (C := k) (mkₐ k (maximalIdeal C))
  obtain ⟨φ, e⟩ := fac π (x - placeTorsionMap (ofId ..) (placeTorsionMap π x))
    (by simp [↓← placeTorsionMap_comp, ↓map_sub])
  simpa [hf, h₁, hf π x l ▸ congr($h₀.1 _)] using congr(f C $e l).symm

variable {k : _} {l} [Field k] [CharP k l] [Fact l.Prime] (f : ℕ) (X Y : Over (Spec ⟨k⟩))

/-- If Spec B is a scheme over a field k of prime characteristic l, then l = 0 in B. -/
lemma natCast_eq_zero_of_over_charP {l B} [CharP k l] (s : Spec B ⟶ Spec ⟨k⟩) :
  (l : B) = 0 := by simp [CharP.cast_eq_zero, ← map_natCast (preimage s).1]

/-- For a scheme X over a field k of prime characteristic l, the absolute l^f-Frobenius X → X,
acting on B-valued points through x ↦ x^{l^f} on B. -/
noncomputable def absFrobenius := (exists_hom_of_cover LineBundle.one (fun _ _ t _ ↦ specMap
  (frobPow (natCast_eq_zero_of_over_charP (t ≫ X.hom)) f) ≫ t)
  (by simp_rw [← Spec.map_comp_assoc]; congr! 2; aesop)).choose

lemma comp_absFrobenius {B} t : t ≫ absFrobenius f X =
  specMap (frobPow (natCast_eq_zero_of_over_charP (B := B) (t ≫ X.hom)) f) ≫ t :=
  Classical.some_spec₂ (t ≫ · = _) (by tauto)

lemma absFrobenius_comm g : absFrobenius f X ≫ g = g ≫ absFrobenius f Y :=
  hom_ext_of_cover LineBundle.one (by simp [← Category.assoc, comp_absFrobenius])

lemma absFrobenius_apply x : absFrobenius f X x = x := by simpa [X.1.fromSpecResidueField_apply]
  using (congr($(comp_absFrobenius f X (X.1.fromSpecResidueField x)) default))

lemma picClass_pull_absFrobenius {ι L} (h : @IsLinearSystem _ ι L) : l ^ f • L.picClass =
  (L.pull (absFrobenius f X)).picClass := picClass_pow
  _ ▸ by apply picClass_eq_of_le (fun _ ↦ ·) <;> simp_all [LineBundle.pow, comp_absFrobenius,
  IsLinearSystem, PointFn.IsRegularOn, of_carrier, LandsIn, LE.le, absFrobenius_apply]

open Over Ideal.Quotient Scheme DualNumber NumberField ThetaObject Obj IsGroupBaseChange
variable {E k : _} [Field E] [CMBase E] {D : PEL E} [Field k] {Z σ : _} {Y :
  ThetaFamily D Z σ} {x₀ : ThetaObject Y _} {x : _} {x'} (hq :
  IsPullbackAlong (sqZeroReduction k k) x₀ x) (hq' : IsPullbackAlong (sqZeroReduction k k) x₀ x')

/-- The T-points y, y' of the lifts x, x' of x₀ to k[ε] have equal images in the abelian scheme
of Y on affine T-schemes where ε = 0. -/
@[local simp] def AgreeModEps T y y' := ∀ B (b : Spec B ⟶ _) (t :
  (Over.mk b).map (sqZeroReduction ..) ⟶ T), x.isGroupBaseChange.pointEquiv (t ≫ y) =
  homMk (𝟙 (Spec B)) ≫ x'.isGroupBaseChange.pointEquiv (t ≫ y')

lemma exists_isSqZeroExt_mod_eps {C} (s : Spec C ⟶ _) : ∃ B ψ b, Spec.map ψ ≫ s =
  b ≫ sqZeroReduction k k ∧ @IsSqZeroExt C B ψ ∧ (∀ a, ψ a = 0 ↔ preimage s ε ∣ a) ∧ ∀ {B t b},
  t ≫ s = b ≫ sqZeroReduction k k → ∃ l : Spec B ⟶ _, l ≫ Spec.map ψ = t := ⟨_, ofHom _, Spec.map
  _ ≫ s ≫ specMap _, homEquiv.injective (by aesop), ⟨Ideal.Quotient.mk_surjective, by simp_all
  [eq_zero_iff_dvd, dvd_def, mul_mul_mul_comm _ _ (preimage s ε), ← map_mul]⟩, eq_zero_iff_dvd _,
  fun {_ t _} w ↦ map_preimage t ▸ le_ker_iff_factors.1 (by simpa using! congr(preimage $w ε))⟩

lemma AgreeModEps.ringChar_smul_and_smul_eq_zero {T y} (h : AgreeModEps hq hq T y 0) :
  ringChar k • y = 0 ∧ ∀ {ψ}, x.baseHom = .comp ψ x₀.baseHom →
  ∀ ⦃b : ℤ⦄ ⦃c⦄, x₀.baseHom (D.β - b) = 0 → x₀.baseHom c = 0 → ((star D.β - b) * c) • y = 0 := by
  constructor <;> intros <;> ext <;> apply hom_ext_of_cover .one fun _ _ t _ ↦ ?_
    <;> let s := t ≫ T.hom <;> choose _ ψ _ w _ _ using exists_isSqZeroExt_mod_eps s <;> let τ :=
    (Over.mk s).homMk t <;> have v : IsInfinitesimal ψ (τ ≫ y) :=
    (by simpa [IsInfinitesimal, eq_zero_iff_factors_zero_section] using h _ _ (homMk _ w ≫ τ))
    <;> exact congr($((by simp [v.nsmul_injective_and_eq_zero x.smoothOfRelativeDimension
    (mkIdTerminal.from _), mul_smul, v.smul, *, natCast_eq_zero_of_over_charP
    (s ≫ (specOver k _).hom), (x.exists_tangent_log _).choose_spec (ψ := ψ)] : τ ≫ _ = τ ≫ 0)).1)

/-- Drinfeld's lifting lemma. Let x, x' deform x₀ over k[ε], and let c in O_E kill all
infinitesimal points of A_x'. Then some homomorphism F: A_x → A_x' reduces to c, and F(y) =
c·y' whenever y and y' agree modulo ε. -/
lemma drinfeld_lift {c : 𝓞 E} (hc : ∀ T y, AgreeModEps hq' hq' T y 0 → c • y = 0) : ∃ F,
  IsAdditive F ∧
  hq.schemeMap ≫ F = c • hq'.schemeMap ∧ ∀ T y' y, AgreeModEps hq' hq T y' y → y ≫ F = c • y' := by
  choose V z ha hV using (exists_isEtaleChart · Y.relative_dim)
  choose C j _ _ hj using
    (@exists_affine_mem_range_and_range_subset _ · (x.toFamily.1 ⁻¹ᵁ _) (ha _))
  choose F h K using by simpa using (exists_hom_of_rel (c • 𝟙 _) (AgreeModEps hq' hq _) (fun a h ↦
    (h · · <| · ≫ a)) (by aesop) (by aesop) (.ofArrows _ j) (zariskiPrecoverage_le_fpqcPrecoverage _
    (by aesop)) fun _ _ ⟨a⟩ ↦ (exists_isSqZeroExt_mod_eps (j a ≫ _)).elim fun _ ⟨ψ, _, e, hψ, _,
    H⟩ ↦ (hV _ (Spec.map ψ ≫ j a ≫ x.toFamily.1) _ (fun _ _ ↦ hj a ⟨_, rfl⟩) (by simp [reassoc_of%
    e, *]) (hψ.1.1.comp_left _).choose_spec).imp' x'.isGroupBaseChange.pointEquiv.2
    fun _ w _ _ t ↦ (H t.w).rec fun _ ↦ (by ext; simp [pointEquiv, ← ·, w.1]))
  use F, h, K _ _ _ fun _ _ _ ↦ by ext; simp [pointEquiv, IsPullbackAlong.comp_toFamily], K
