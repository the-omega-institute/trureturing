import OmegaMath.NumberTheory.GRH.Lib.ClassField.GaloisCohomology.CupProduct
import OmegaMath.NumberTheory.GRH.Lib.ClassField.Places.UnramifiedCharacters
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Galois cohomology in degrees ≤ 2: Shapiro, Hilbert 90, Kummer, symbols, Herbrand
quotient (known result; see Lib.ClassField.GaloisCohomology.CyclicNorm).

This file: Shapiro's lemma in degrees 0–2, corestriction, cor∘res = index, projection formula for
symbols. Hilbert 90 for continuous cocycles, Kummer cocycles, cup product as cyclic symbol. Sylow
reduction of H² statements to cyclic steps of prime degree. -/

open DFunLike DiscreteModule DistribSMul Fintype Function MulAction NeZero QZ QuotientGroup Set
  Subgroup DiscreteUnits

variable {R Γ H} [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H]
  {M : DiscreteModule R Γ} [CompactSpace Γ] (U : OpenSubgroup Γ) [TopologicalSpace H] (φ : H →ₜ* Γ)
  {U' : Subgroup Γ} {Γ' K Ω} [Group Γ'] [TopologicalSpace Γ'] [Field K] [Field Ω] [Algebra K Ω]
  [MulSemiringAction Γ' Ω] [IsProGalois Γ' K Ω] {Γ₁ : Type} [Group Γ₁] [TopologicalSpace Γ₁]

/-- For a continuous homomorphism φ: H → Γ, the additive map from continuous ℚ/ℤ-valued
characters of Γ to those of H, χ ↦ χ∘φ. -/
noncomputable def QZChar.comap : QZChar Γ →+ QZChar H := pairMapZ1 φ .id

lemma QZChar.exists_ker_eq_of_isCyclic [U.Normal] (h : IsCyclic (Γ ⧸ U.1)) : ∃ χ, ker χ = U.1 :=
  ⟨ofZModCocycle _ ⟨((zmodCyclicMulEquiv h).symm · |>.toAdd), by fun_prop, by simp⟩, by
  ext; exact (map_eq_zero_iff _ ofZMod_injective).trans (by simp [MulEquiv.symm_apply_eq])⟩

namespace DiscreteModule

lemma funModule_apply_one (u : U.1) F : (M.funModule U).ρ u F ⟦1⟧ = (M.restrictTo U).ρ u (F ⟦1⟧) :=
  congrArg (_ ∘ F) (by simp [QuotientGroup.eq])

/-- The Shapiro map on continuous 1-cocycles, Z¹(Γ, Fun(Γ/U, M)) → Z¹(U, M): restrict to U and
evaluate at the trivial coset. -/
abbrev shapiroZ1 :=
  pairMapZ1 (ρ := (M.funModule U).ρ) (subgroupIncl _) (.proj _) (M.funModule_apply_one U)

/-- The linear map H²(Γ, Fun(Γ/U,M)) → H²(U,M) given by restriction to U followed by evaluation
at the identity coset. -/
abbrev shapiroH2 :=
  pairMapH2 (ρ := (M.funModule U).ρ) (subgroupIncl _) (.proj _) (M.funModule_apply_one U)

/-- The norm from the open subgroup U to Γ: for a U-invariant y in M, the sum of g·y over chosen
representatives g of the cosets Γ/U. -/
noncomputable abbrev corestrictH0 (y : (M.restrictTo U).H0) := M.sum U (M.ρ ·.out y)

omit [IsTopologicalGroup Γ] [CompactSpace Γ] in
/-- For U open in Γ there is s : Γ/U → Γ with s = 1 at the trivial coset, s(x) in the coset x,
and s(x)⁻¹ g s(g⁻¹x) ∈ U for all x and g. -/
lemma exists_coset_section : ∃ s : Γ ⧸ U.1 → Γ, (∀ g ∈ U.1, s g = 1) ∧ (∀ x, (s x)⁻¹ • x = ⟦1⟧) ∧
  ∀ x g,
  (s x)⁻¹ * g * s (g⁻¹ • x) ∈ U.1 := ⟨(·.out * (@QuotientGroup.mk _ _ U 1).out⁻¹), by simp_all [←
  eq_inv_smul_iff, ← SetLike.ext_iff.1 (stabilizer_quotient U.1), mul_smul, -stabilizer_quotient]⟩

/-- Shapiro's lemma in degree zero: for U open in Γ, every Γ-equivariant function Γ ⧸ U → M has
the form gU ↦ g·y for some U-invariant y in M. -/
lemma shapiro_H0 (F : (M.funModule U).H0) : ∃ y : (M.restrictTo U).H0, (M.ρ ·.out y) = F.1 :=
  ⟨⟨_, (by rw [← funModule_apply_one,
  F.2 ·])⟩, by ext x; simpa [← Quotient.mk_smul_out] using congrFun (F.2 x.out) x⟩

lemma shapiro_H1 (F : Z1 (M.funModule U).ρ) m (h : ∀ u : U.1, F.1 u ⟦1⟧ = M.ρ u m - m) :
    ∃ n, ∀ g, F.1 g = ρ _ g n - n := ⟨Quotient.lift (fun g ↦ M.ρ g m - F.1 g g) (by
  rintro _ g ⟨⟨u, e⟩, ⟨⟩⟩; simp [F.2.2, mk_mul_of_mem g e, h ⟨_, e⟩]; abel),
  (funext <| forall_mk.2 <| mul_left_surjective · |>.forall.2 (by simp [F.2.2]))⟩

/-- Shapiro's lemma in degree two, injectivity: for U open in the compact group Γ, the map H²(Γ,
Fun(Γ/U, M)) → H²(U, M), restriction followed by evaluation at the trivial coset, is
injective.

Known result: Galois cohomology in degrees ≤ 2: Shapiro, Hilbert 90, Kummer, symbols, Herbrand
quotient. -/
lemma shapiroH2_injective : Injective (M.shapiroH2 U) := .of_ker _ (by
  have ⟨s, _, _, m⟩ := exists_coset_section U; let t x g : U := ⟨_, m x g⟩
  rintro ⟨F, _, q⟩; repeat erw [QuotientAddGroup.eq_zero_iff]
  refine fun ⟨c, _, (_ : ∀ a b : U, F (a, b) _ = M.ρ a _ - _ + _)⟩ ↦ ⟨fun g x ↦ M.ρ (s x) (c (t x
    g)) - F (s x, t x g) x + F (g, s (g⁻¹ • x)) x, by fun_prop, fun g k ↦ ?_⟩; ext x
  have := congr($(q (s x) (t x g) (t (g⁻¹ • x) k)) x); simp [*, -q] at this
  simp_all [t, mul_assoc, mul_smul]; grind)

lemma index_smul_eq_sum_const m : U.index • m = M.sum U fun _ ↦
  m := by simp [sum, card_eq_nat_card]; rfl

/-- Let U be open in the compact group Γ, β ∈ H²(Γ, Fun(Γ/U, M)), α ∈ H²(Γ, M). If the Shapiro
image of β in H²(U, M) is the restriction of α, then summing values over Γ/U sends β to
[Γ:U]·α. -/
lemma mapH2_sum_eq_index_smul β α : M.resH2 _ α = M.shapiroH2 U β → (M.sum _).mapH2 β =
  U.index • α := α.ind' fun x (h : ⟦_⟧ = _) ↦ shapiroH2_injective U (a₁ :=
  (const ..).mapH2 ⟦x⟧) h ▸ .symm congr(⟦$(by ext; apply index_smul_eq_sum_const)⟧)

lemma cyclicClass_corestrictH0 χ w {v : M.H0} (e : M.corestrictH0 U w = v) α (a : M.resH2 _ α =
  cyclicClass _ (QZChar.comap (subgroupIncl U) χ) w) : cyclicClass _ χ v =
  U.index • α := have h g : M.ρ (@QuotientGroup.mk _ _ U g).out w = M.ρ g
                                               w := by cases mk_out_eq_mul U g; simp [*]; erw [w.2]
  mapH2_sum_eq_index_smul U (cyclicClass _ χ ⟨(M.ρ ·.out w), by simp [funext_iff, forall_mk, h]⟩) _
    (a.trans congr(⟦$(by ext; simpa using! congrArg _ (h 1).symm)⟧)) ▸ congr(⟦$(by aesop)⟧)

lemma index_smul_eq_zero_of_resH2 {x} : M.resH2 U x = 0 → U.index • x = 0 :=
  (mapH2_sum_eq_index_smul U 0 _ · ▸ by simp)

omit [IsTopologicalGroup Γ] [CompactSpace Γ] in
/-- Let w = k·r be a Γ-invariant element of M. The class δχ ∪ w in H²(Γ,M) restricts to zero on
every subgroup U that fixes r and on which kχ vanishes. -/
lemma resH2_cyclicClass_eq_zero {χ k r} : ∀ {w : M.H0}, (k : ℕ) • r = ↑w → (∀ g : U', M.ρ g r = r ∧
  k • χ.1 g = 0) → M.resH2 U' (cyclicClass _ χ w) = 0 | ⟨_, _⟩, rfl, h => (by erw [map_nsmul
  (cyclicClass _ (QZChar.comap _ χ)) k ⟨r, (h · |>.1)⟩, ← AddMonoidHom.flip_apply, ← map_nsmul,
  bot_le (a := AddMonoidHom.ker _) (by ext; exact (h _).2)])

instance _root_.isGalois_fixedFieldOf (U : Subgroup Γ') [U.Normal] : IsGalois K (fixedFieldOf
  U) where to_normal := IntermediateField.normal_iff_forall_map_le'.2 ((toAlgAut_surjective
  Γ').forall.2 (image_subset_iff.2 fun _ ↦ smul_mem_fixedPoints_of_normal ·))

/-- Let w ∈ Ω^× be Γ-invariant, a^n = w, and ξ: Γ → ℤ/n a continuous homomorphism. The 2-cocycle
(g,h) ↦ (ga/a)^{ξ(h)} has class −δ(ξ/n) ∪ w. -/
lemma _root_.kummer_cup_eq_neg_cyclicClass {n} [NeZero n] {w a} (ha : n • a = ↑w) ξ z (hz : ∀ g h,
  z.1 (g, h) = (ξ.1 h).val • (unitsRep g a - a)) : ⟦z⟧ = -cyclicClass (@unitsRep Γ' Ω _ _ _)
  (QZChar.ofZModCocycle n ξ) w :=
  (Submodule.Quotient.eq _).2 ⟨(·.val • a) ∘ _, continuous_bot.comp ξ.2.1, by
  simp_all [ξ.2.2, ← ha]; intros
  match_scalars <;> qify [← map_add]; grind [ofZMod_apply, QZ.fracRep_mk,
    natCast_ne, Int.fract_div_natCast_eq_div_natCast_mod, Nat.mod_eq_of_lt]⟩

include K in
/-- Hilbert's Theorem 90: for Γ = Gal(Ω/K), every continuous 1-cocycle f of Γ with values in Ω^×
is a coboundary, f(g) = gm/m for some m. -/
lemma _root_.hilbert90_unitsRep (f : SubmoduleElem (M := Γ' → DiscreteUnits Ω) (Z1 unitsRep))
    : ∃ m, ∀ g, f.1 g = unitsRep g m - m := have := f.2.2 1
  (exists_openNormalSubgroup_apply_eq (Y := Γ') f.2.1.fst').rec fun U H ↦ (not_subset.1 (one_ne_zero
    ∘ Submodule.mem_span.1 (mem_span_fixed (.id _) ⟨⟨fun g ↦ (f.1 g).toMul.1 • toLinearMap ℤ Ω g, by
       aesop⟩, by simp [ext_iff, f.2.2, mul_smul]⟩ (by simp [field]) (by aesop)
    (fixingSubgroup_fixedFieldOf U.1.1).le) ⊥)).rec fun x ⟨h, e⟩ ↦
    ⟨-DiscreteUnits.ofNeZero x e, by simpa [DiscreteUnits.ext_iff, field, -val_unitsRep] using! h⟩

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [MulSemiringAction Γ₁ Ω]
  [IsProGalois Γ₁ K Ω]

/-- Kummer cocycle: for Ω algebraically closed of characteristic 0, Γ = Gal(Ω/K) fixing the n-th
roots of unity, ζ a primitive one and x in Ω^× fixed by Γ, there are a with a^n = x and a
continuous homomorphism f : Γ → ℤ/n with ga/a = ζ^{f(g)}. -/
lemma _root_.exists_kummer_cocycle [IsAlgClosed Ω] [CharZero Ω] {n} [NeZero n] (e : ∀ g : Γ₁,
  cycCharMod Ω n g = 1) (x : (unitsModule Γ₁).H0) : ∃ᵉ (a) (f : Z1 (.trivial ℤ Γ₁ _)), n • a = x.1 ∧
  ∀ b, n • b = x.1 → ∀ g,
  (rootPowHom Ω n).1 (f.1 g) = unitsRep g b - b := have := (rootPowHom Ω n).2
  (exists_nsmul x out).imp fun a h ↦ by use ⟨invFun (rootPowHom Ω n).1 ∘ _,
    continuous_bot.comp (coboundary _ a).2.1, ?_⟩,
    h <;> simp_all [← this.1.eq_iff, invFun_eq, smul_sub, ← map_nsmul, x.2 _, -Additive.forall,
    ← sub_eq_iff_eq_add, cycCharMod_eq_one_iff, sub_eq_sub_iff_sub_eq_sub, ← map_sub]

/-- Y contains the coboundaries of Γ in M and, for each cocycle y ∈ Y' of U, a corestriction of
y: the sum over Γ/U of a Shapiro lift. -/
def HoldsCorestrictions (Y' : AddSubgroup (Z1 (M.restrictTo U).ρ)) (Y : AddSubgroup (Z1 M.ρ)) :=
  (∀ m, M.coboundary m ∈ Y) ∧ ∀ y ∈ Y', ∃ F, M.shapiroZ1 U F = y ∧ (M.sum _).mapZ1 F ∈ Y

omit [IsTopologicalGroup Γ] [CompactSpace Γ] in
lemma resH2_swap {U V α} : (M.restrictTo V).resH2 (subgroupOf U V) (M.resH2 _ α) = 0 →
  (M.restrictTo U).resH2 (V.subgroupOf U) (M.resH2 _ α) = 0 := α.ind' fun _ ↦ (pairMapH2 (.mk
  (.mk' (fun g ↦ ⟨⟨_, g.2⟩, g.1.2⟩ : V.subgroupOf U → U.subgroupOf V) (by simp))) _).congr_arg

/-- Let α in H²(Γ, M) die on open normal W. Suppose that for open U ⊇ W and open normal V ⊇ W of
prime index in U, if α − s (s in S) dies on V, some α − s' dies on U. Then α ∈ S. -/
lemma mem_of_prime_step (S : AddSubgroup _) {α} {W : OpenSubgroup Γ} [W.Normal] (w :
  M.resH2 W α = 0) (h : ∀ U (V : OpenSubgroup U.1) [V.Normal], W ≤ U → W.1.subgroupOf U ≤ V →
  V.index.Prime → ∀ s ∈ S, (M.restrictTo U).resH2 V (M.resH2 _ (α - s)) = 0 → ∃ s ∈ S,
  M.resH2 U (α - s) = 0) : α ∈ S := by simpa using
  ((addOrderOf (QuotientAddGroup.mk' S α)).eq_one_iff_not_exists_prime_dvd.2 fun l p d ↦ by
  obtain ⟨i, K, ⟨n, ⟨s, t, q⟩, k⟩, m⟩ := le_comap_mk' W.1, {L | ∃ n, comap (mk' W.1) L ∈ {U | ∃
    s ∈ S, M.resH2 U (α - s) = 0} ∧ .card L = l ^ n}.toFinite.exists_maximal ⟨⊥, 0, by aesop⟩
  have o {L} := isOpen_mono (i L) W.2
  let ⟨L, c, e⟩ := Sylow.exists_subgroup_card_pow_succ (hp := ⟨p⟩) (by
    grw [pow_succ, ← k, d, addOrderOf_dvd_of_nsmul_eq_zero, card_mul_index]
    simpa [(QuotientAddGroup.eq_zero_iff _).2 t,
      index_comap] using congr(QuotientAddGroup.mk' S $(index_smul_eq_zero_of_resH2 ⟨_, o⟩ q))) k
  have r := by simpa [*, pow_add, p.ne_zero] using relIndex_mul_relIndex _ _ _ bot_le e
  exact p.ne_one (r ▸ relIndex_eq_one.2 (m ⟨_, @h ⟨_, o⟩ ⟨_, subgroupOf_isOpen _ _ o⟩
    ((normal_of_index_eq_minFac_card (r.trans (by grind [p.pow_minFac]))).comap (.subgroupComap
    ..)) (i _) (@i _ ·) (by simp [← relIndex.eq_1, relIndex_comap, map_comap_eq_self, *]) _ t
    (resH2_swap (q ▸ rfl)), c⟩ e)))
