import GRH.Lib.ClassField.Places.AdeleNorm
import GRH.Lib.ClassField.LocalDuality.RealPlaceSymbols
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Local class field theory, covering the invariant of the Brauer group, the Artin
map, norms and the tame symbol. It is proved here for henselian fields such as fixed fields of
decomposition groups, and the norm index in prime degree comes from Tate's lemma on the Herbrand
quotient. The Artin map sends uniformisers to geometric Frobenii. Source: J.-P. Serre, Local Fields
(1979), XII–XIV; J. S. Milne, Class Field Theory (v4.03), I and III 2.

This file: Local Artin map: norm functoriality, density, units to inertia, tame symbol, tame
generator. -/

attribute [-simp] map_smul one_apply


open Filter WithZero Units Module LinearMap Classical Subgroup DFunLike QZChar IsProGalois Valued
variable {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [NumberField K] {w : FinPlace K}

/-- For a finite place w of a number field K and n ≠ 0, every subgroup T of K_w^× that contains all
n-th powers is open. -/
lemma isOpen_of_forall_pow_mem {n} (hn : n ≠ 0) {T : Subgroup (LocField w)ˣ} (h : ∀ y, y ^ n ∈ T) :
    T.IsOpen := let := toNontriviallyNormedField (LocField w) _
  T.isOpen_of_mem_nhds ((nhds _).3 (continuous_val.tendsto (1 ^ n) (((hasStrictDerivAt_pow
  ..).map_nhds_eq (by simpa)).ge range_mem_map)) fun x ⟨y, e⟩ ↦ (ext e).subst (h (x.ofPow y hn e)))

/-- Every homomorphism from K_w^× to the topological abelianisation of a profinite group is
continuous. -/
lemma continuous_hom_locField_units [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ] (f : (LocField w)ˣ →* TopologicalAbelianization Γ) : Continuous f :=
  continuous_iff_isOpen_ker.2 fun χ ↦
  isOpen_of_forall_pow_mem (quotient_finite_of_isOpen _ ((continuous_abelianLift χ).1 {1} ⟨⟩)
  ).card_pos.ne' (f.map_pow · _ ▸ (abelianLift χ).ker.pow_index_mem _)

variable [Algebra K Ω]

/-- The union of the inertia groups in Gal(Ω/K) of all valuation subrings of Ω lying over a
prime of the set S of primes of K. -/
def inertiaAbove (S : Set (FinPlace K)) :=
  {g | ∃ v ∈ S, ∃ A : ClosurePlace, IsPlaceOver A v ∧ g ∈ inertiaGroup Gal(Ω/K) A}

namespace IsPlaceOver

variable [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω] {A : ClosurePlace} (h : IsPlaceOver A w)

include h

/-- For A over w and an embedding of Ω in ℚ̄_p inducing A, f = `localArtin` satisfies χ(f
x) = −inv(χ, x): on K_w^× for the invariant of K_w, and on K^× for the invariant of the
decomposition field of A. -/
lemma isLocalArtin_localArtin {p} [Fact p.Prime] [Algebra (LocField w) (PadicAlgCl p)] {j}
    (F : IsCompletionEmb w p Γ A j) : let f := localArtin Γ A w
  IsLocalArtin _ (LocField w) (intQpBar p) f ∧
    IsLocalArtin _ (fixedFieldOf (decompGroup Γ A)) A (f.comp (map (algebraMap K _).1)) := by
  obtain ⟨⟨L⟩, ⟨f, e⟩, π, hπ, u⟩ := h.decompGroup_spec Γ, exists_hom_abelianLift_eq (((-cyclicClass
    _).compr₂ (AddEquiv.ofBijective _ F.classOfInv_bijective).symm.toAddMonoidHom).flip.comp
    (DiscreteUnits.ofBase (K := LocField w) ..)), h.exists_uniformiser Γ
  suffices _ from have G := @epsilon_spec _ (IsLocalArtin _ _ A <| .comp · _) ⟨f, this⟩
    ⟨by simp [IsLocalArtin, e, (continuous_hom_locField_units (localArtin ..)).ext_on
      ((w.denseRange_algebraMap K).preimage isOpenMap_val) (continuous_hom_locField_units f) fun y
      ⟨x, e⟩ ↦ abelianization_ext (L.isClassOfInv_classOfInv.1 <| by
      erw [← ext (u := .map _ (mk0 x (by grind [ne_zero]))) e, G ·, this])], G⟩
  refine fun χ x ↦ (L.classOfInv_bijective.2 _).rec fun s t ↦
    .trans (congrArg _ (F.isClassOfInv_classOfInv.1 ?_)) t
  simp [*, ← one_nsmul s ▸ L.pairMapH2_classOfInv (L' := F.2) (f := 1) (.id _) j F.comap_eq
    F.equivariant ⟨u.ordRat_eq_one L, (congrArg _ (ext (F.map_algebraMap π))).trans
    ((F.isUniformiser_iff.2 (hπ ▸ v_algebraMap_eq_valuation _)).ordRat_eq_one F.2
    (π := π.map _))⟩ (by bound [F.residueCard_eq]) s]
  exact congr(⟦$(by ext; simp [F.map_algebraMap])⟧)

/-- Let A lie over w in K, j: Ω → Ω extend k → K. If jg = g'j and Art_w y = g', the local norm of y
has symbol g. If ker χ consists of the g admitting such g', χ(Art x) = 0 makes x a local norm from
K_w.

Known result: Local class field theory: invariant of the Brauer group, Artin map, norms, tame
symbol. -/
lemma localArtin_adeleNorm {Γ' k : Type} [Group Γ'] [TopologicalSpace Γ'] [Field k]
  [EmbeddedNumberField k] [MulSemiringAction Γ' Ω] [IsProGalois Γ' k Ω] [Algebra k K] (ψ : Γ →* Γ')
  (j : Ω →+* Ω := 1) (hψ : ∀ g x, j (ψ g • x) = g • j x := by tauto) (hj : ∀ x, j (algebraMap k Ω
  x) = algebraMap K Ω (algebraMap k K x) := by simp) : (∀ {y} {g : decompGroup Γ A}, localArtin Γ A
  w y = g → localArtin Γ' (A.comap j) _ (localNorm k w y) = (⟨_, decompGroup.map hψ g.2⟩ :
  decompGroup ..)) ∧ ∀ {χ x}, (∀ g' : decompGroup Γ' (A.comap j), χ.1 g' = 0 ↔ ∃ g : decompGroup Γ
  A, ψ g = g') → abelianLift χ (localArtin Γ' _ _ x) = 1 → ∃ y, localNorm k w y = x := by
  set u := w.below k
  algebraize [locMap _ (refl u), evalAt u, (locMap _ rfl).comp (evalAt u)]
  let π := (⟨evalAt w, by aesop⟩ : _ →ₐ[𝔸f k] _).toLinearMap.liftBaseChange (LocField u)
  let ε := π.quotKerEquivOfSurjective (⟨1 ⊗ₜ singleAdele w ·, by aesop⟩)
  have N {y} : localNorm k w y = y.map (Algebra.norm (LocField u)) :=
    let M := (mulLeft (𝔸f k) (locIdele w y).1).baseChange (LocField u)
    have : ∀ x ∈ π.ker, M x = x := (TensorProduct.mk_surjective _ _ _
      (⟨singleAdele u ·, dite_eq_left
      rfl⟩)).forall.2 fun z h ↦ congr(1 ⊗ₜ $(ext_iff.2 ((and_forall_ne w).1 (by aesop))))
    ext ((det_baseChange _).symm.trans ((det_conj _ ε.symm).subst (by
    erw [M.det_eq_det_mul_det π.ker (by aesop_cat), (by bound : M.restrict _ = 1)]
    simp; congr with
    exact ε.eq_symm_apply.2 (by aesop : π (1 ⊗ₜ _) = _ * π (1 ⊗ₜ _)))))
  obtain ⟨_, _, _, a, i, ⟨F⟩⟩ := Finite.equiv ε, h.exists_isCompletionEmb Γ
  algebraize [a.2.comp (locMap _ (refl u))]
  obtain ⟨_, ⟨f⟩⟩ := F.2.1, nonempty_isCompletionEmb_of_isPadicAt Γ' (v :=
    u) (i.comp j) ⟨F.continuous.comp (by fun_prop), congr(($F.valRingBelow_eq).comap _).trans
    (by ext; apply v_locMap_le_one), congr(($F.comap_eq).comap j),
    by simp_all [F.map_algebraMap, ← locMap_algebraMap]; tauto⟩
  obtain ⟨_, ⟨φ, hφ⟩, E, -⟩ := f.2.1, exists_galois_restrict _ (G :=
    f.2.1) (decompGroup Γ A) (.id _) fun g _ ↦ smul_algebraMap g (_ : LocField w),
    isLocalArtin_localArtin (by simp [hj ·, ← h _, u, val_comap_lt_one]) f
  have o := Fact.mk (φ.coe_range ▸ (isOpenEmbedding_galois_restrict _ hφ).2)
  have := of_fixingSubgroup_eq (isClosedEmbedding_galois_restrict _ hφ).2.1.symm
  simp_rw [fun g : decompGroup Γ A ↦ show ψ g = φ g from (IsGaloisGroup.faithful k).1 fun _ ↦
    j.injective (i.injective (by erw [hψ, F.equivariant, f.equivariant, ← hφ]; rfl))]
  use fun hy ↦ abelianization_ext fun χ ↦ f.isClassOfInv_classOfInv.1 ?_, fun h hx ↦
    ((cyclicClass_eq_zero_iff_norm (J := (ext (by simpa using! h) : QZChar.ker _ =
    φ.range) ▸ this) _).1 (neg_eq_zero.1 (E .. ▸ hx ▸ map_zero _))).imp fun _ ↦ N.trans
  obtain ⟨⟨_, ⟨⟨_, _, ⟨⟨b, q, _⟩⟩⟩⟩⟩, P⟩ := f.of_finite ⟨_, o.1⟩ _,
    (f.isUniformiser_iff.2 (v_uniformizer _)).ordRat_eq_one f.2
  choose r s using f.exists_resH2_classOfInv_eq ⟨_, o.1⟩
  erw [N, E, DiscreteModule.cyclicClass_corestrictH0 _ χ _ (corestrictH0_ofBase_eq_norm ..) _ (s _),
    ← map_nsmul, ← map_neg, f.isClassOfInv_classOfInv.1.eq_iff,
    ← F.isClassOfInv_classOfInv.1.eq_iff, map_neg, ← (b ▸ f.pairMapH2_classOfInv φ (.id _) rfl hφ
    ⟨P, by simp [*]⟩ q :), (Quot.ind (by bound) : ∀ x y, (unitsModule _).resH2 _ x = y →
    pairMapH2 φ _ _ x = pairMapH2 ⟨φ.rangeRestrict, φ.2.subtype_mk _⟩ .id _ y) _ _ (s _),
    ← (h.isLocalArtin_localArtin F).1 (comap φ _), hy]; bound

/-- For A lying over w, the local Artin map from K_w^× to the abelianised decomposition group of A
has dense image. -/
lemma denseRange_localArtin :
  DenseRange (localArtin Γ A w) := have ⟨p, _, _, _, ⟨F⟩⟩ := h.exists_isCompletionEmb Γ
  Quot.ind (mem_of_forall_abelianLift (MonoidHom.range _).isClosed_topologicalClosure _ fun χ H ↦
    char_eq_zero_of_cyclicClass_eq_zero
    (by simpa [H _ (subset_closure ⟨_, rfl⟩)] using (h.isLocalArtin_localArtin F).1 χ) ·)

/-- For A lying over w and a uniformiser x of K_w, the local Artin symbol of x is the class of s⁻¹
for some arithmetic Frobenius s in the decomposition group of A. -/
lemma exists_frob_inv_eq_localArtin {x} (hx : v x.1 = exp (-1)) : ∃ s : decompGroup Γ A, IsFrob A
  w.q s.1 ∧ localArtin Γ A w x = s⁻¹ := (h.exists_isCompletionEmb Γ).elim fun _ ⟨_, _, _, ⟨F⟩⟩ ↦
  ((h.isLocalArtin_localArtin F).1.exists_frob_of_isUniformiser (F.isUniformiser_iff.2 hx)).imp
  fun _ ↦ .imp_left (F.residueCard_eq ▸ F.comap_eq ▸ ·.map F.equivariant)

/-- The local Artin map sends units into inertia: for A over w and a unit x of K_w, the Artin image
of x is the class of an element of the inertia group of A. -/
lemma exists_inertia_eq_localArtin {x} (hx : v x.1 = 1) : ∃ s : decompGroup Γ A, ↑s ∈ inertiaGroup Γ
  A ∧ localArtin Γ A w x = s := (h.exists_frob_inv_eq_localArtin (v_uniformizer w)).rec fun φ H ↦
  (h.exists_frob_inv_eq_localArtin (x := x * uniformizer w) (by simpa)).imp'
  (·⁻¹ * φ) (by simp_all [← eq_div_iff_mul_eq', IsFrob.inv_mul _ H.1])

/-- For A lying over w, if s in the decomposition group acts on residues as the (N w)^n-th
power, n ≥ 0, then its class is the local Artin symbol of some x ∈ K_w^× of order −n. -/
lemma exists_localArtin_eq {q g} (hs : IsFrob A q g⁻¹) (n : ℕ) (e : q = w.q ^ n := by simp) : ∃ x,
    v x.1 = exp (-↑n) ∧ localArtin Γ A w x = ⟦⟨g, inv_mem_iff.1 hs.1⟩⟧ := by
  obtain ⟨⟨_, ⟨q⟩⟩, φ, hφ, H⟩ := h.decompGroup_spec Γ,
    h.exists_frob_inv_eq_localArtin (Γ := Γ) (v_uniformizer w)
  exact (mem_of_forall_abelianLift (H := .map _ (.map _ _)) ((isCompact_idelesUnitOff_empty.image
    (by fun_prop)).image (continuous_hom_locField_units _)).isClosed ⟦⟨_, inv_mem hs.1⟩ * φ ^ n⟧
    fun χ hχ ↦ have ⟨ψ, ⟨hψ, k⟩, _⟩ := existsUnique_unramified_char (q ▸ hφ) _
    (h.denseRange_localArtin.eq fun x ↦ (mul_mem_cancel_right (zpow_mem (by simpa [H] :
      uniformizer w ∈ ((abelianLift ψ).eqLocus _).comap _) (v x.1).log)).1
      (.trans ((h.exists_inertia_eq_localArtin (by simp [exp_neg, -inv_exp])).rec fun t a ↦ a.2 ▸ hψ
        t a.1) (hχ _ ⟨_,
      ⟨_, locIdele_mem_idelesUnitOff (by simp [exp_neg, -inv_exp]), ideleAt_locIdele ..⟩,
      rfl⟩).symm)) _ ▸
    hψ _ (hs.inv_mul (e ▸ hφ.pow n))).imp' (· * uniformizer w ^ n) (by aesop)

/-- For A lying over w, if the local Artin symbol of x is the class of g in the abelianised
decomposition group of A, then `artinAt` sends x to the class of g in the abelianisation of Γ. -/
lemma artinAt_eq_of_localArtin_eq {x} {g : decompGroup Γ A} (hg : localArtin Γ A w x = g) :
  artinAt Γ w x = g := by
  choose t e using h.exists_smul Γ w.isPlaceOver_placeOver
  rw! [artinAt, ← e, smul_eq_comap]
  exact .trans (by exact congrArg _ (.trans (congrArg _ (Units.ext (by
    simpa [finAdeleIncl] using! congr($(adeleNorm_finAdeleIncl K K (locIdele w x)) w).symm)))
    ((h.localArtin_adeleNorm
    (MulAut.conj t).toMonoidHom _ (by simp [mul_smul])).1 hg))) (mul_inv_cancel_comm ↑t _)

lemma abelianLift_artinAt χ x : abelianLift χ (artinAt Γ w x) =
  abelianLift (comap (subgroupIncl _) χ) (localArtin Γ A w x) :=
  (Quot.exists_rep _).rec fun _ e ↦ (h.artinAt_eq_of_localArtin_eq e.symm).substr (e ▸ rfl)

lemma abelianLift_artinAt_principal χ x : classOfInv _ (fixedFieldOf (decompGroup Γ A)) A
  (abelianLift χ (artinAt Γ w (ideleAt w (principalIdele x)))).toAdd = -(unitsModule Γ).resH2
  (decompGroup Γ A) (cyclicClass _ χ (DiscreteUnits.ofBase Γ Ω (.ofMul x))) :=
  (h.exists_isCompletionEmb Γ).rec fun _ ⟨_, _, _, ⟨F⟩⟩ ↦
  h.abelianLift_artinAt χ _ ▸ (h.isLocalArtin_localArtin F).2 ..

lemma abelianLift_artinAt_eq_one_iff {χ x} : abelianLift χ (artinAt Γ w
  (ideleAt w (principalIdele x))) = 1 ↔ (unitsModule Γ).resH2 (decompGroup Γ A) (cyclicClass _ χ
  (DiscreteUnits.ofBase Γ Ω (.ofMul x))) = 0 := (map_eq_zero_iff _ (h.decompGroup_spec
  Γ).1.isClassOfInv_classOfInv.1).symm.trans (h.abelianLift_artinAt_principal χ x ▸ neg_eq_zero)

open Valuation

attribute [-simp] _root_.valuation_intQpBar_lt_one_iff in
/-- Tame symbol: let π ∈ K be a uniformiser at A over w, y^(N w − 1) = π, and u a unit of K_w with
local Artin symbol s. Then for x ∈ K, u ≡ x at w iff sy/y ≡ x at A. -/
lemma localArtin_tame_symbol {π} (hπ : IsUniformiser A π) {s : decompGroup Γ A} {u} (hu :
  v u.1 = 1) (e : localArtin Γ A w u = s) {y} (hy : y ^ (w.q - 1) = algebraMap K Ω π) {x} :
  v (u.1 - algebraMap K _ x) < 1 ↔ A.valuation (s.1 • y / y - algebraMap K Ω x) < 1 := by
  obtain ⟨a, p, _, b, j, ⟨F⟩⟩ := v_algebraMap_eq_valuation π ▸ h.isUniformiser_iff.1 hπ,
    h.exists_isCompletionEmb Γ
  obtain ⟨_, hF, q, hv, rfl, d⟩ := F.2.1, (h.isLocalArtin_localArtin F).1, F.residueCard_eq,
    map_one_sub_of_lt _ (F.residueCard_eq ▸ valuation_residueCard_lt_one), F.comap_eq,
    (isEquiv_iff_valuationSubring ..).2 F.valRingBelow_eq
  refine ((((intQpBar p).valuation.ltAddSubgroup 1).add_mem_cancel_left (x := j (s.1 • y / y) - b.2
    u.1) ?_).trans d.lt_one_iff_lt_one).symm.trans (by simp [F.map_algebraMap, val_comap_lt_one])
  let ϖ := mk0 _ (ne_zero_of_map (a ▸ exp_ne_zero))
  apply_fun j at hy
  cases' _ : w.q with n <;> simp_all [F.map_algebraMap]
  obtain ⟨⟨_, n0⟩, φ, ⟨hφ⟩⟩ := ne_zero_of_tame_root (π := ϖ) hv hy,
    hF.exists_frob_of_isUniformiser (π := ϖ) (F.isUniformiser_iff.2 a)
  have e : ∀ g, cycCharMod _ n g = 1 := (F.frobenius_spec.2.1 hφ).eq
    (by simp_all [cycCharMod_of_mem_inertiaGroup _ hv, hφ.cycCharMod_eq,
    ← val_inj]) (.of_isOpen_ker _ isOpen_ker_cycCharMod.1)
  choose a f ha hf using
    (exists_kummer_cocycle e <| DiscreteUnits.ofBase (K := LocField w) _ _ <| .ofMul ·)
  have := (kummer_cup_eq_neg_cyclicClass (ha u) (f ϖ) _ ?_).symm.trans ((cupProduct_flip (W :=
    unitsModule _) (M := .of (.trivial ..)) (.compr₂ .mul (rootPowHom _ n).1) ?_ (f ϖ) (f u)).trans
    (neg_inj.2 (kummer_cup_eq_neg_cyclicClass (ha ϖ) (f u) _ ?_)))
  all_goals simp_all [← map_cycCharMod_mul, ← hf _ _ (ha _), ← map_nsmul, mul_comm, ← hF _,
    DiscreteUnits.ext_iff,
    F.isClassOfInv_classOfInv.1.eq_iff, QZ.ofZMod_injective.eq_iff, -Subtype.forall]
  simp [← d.eq_one_iff_eq_one, ← ha, n0.1] at hu
  erw [F.equivariant, ← hf ϖ (.mk0 _ (by simpa)) hy, this, hf _ _ (ha _)]
  simpa [div_sub', pow_succ', *] using hφ.2 _ hu.le

end IsPlaceOver

namespace IsPlaceOver

open Valuation

variable {A : ClosurePlace} (h : IsPlaceOver A w) [IsGalois K Ω]

include h

/-- A tame generator exists: for A over w, some γ in the inertia group has, for every n prime to w,
a uniformiser π ∈ K and y with yⁿ = π and γy/y a primitive n-th root of unity. -/
lemma exists_tameGenerator : ∃ γ : inertiaGroup Gal(Ω/K) A, ∀ n : ℕ, A.valuation n = 1 → ∃ π : Kˣ,
  ∃ y, IsUniformiser A π.1 ∧ y ^ n = algebraMap K Ω π ∧ IsPrimitiveRoot (γ • y / y) n := by
  obtain ⟨⟨G⟩, π, a, u⟩ := h.decompGroup_spec Gal(Ω/K), h.exists_uniformiser Gal(Ω/K)
  choose y O using fun n : {n : ℕ // A n = 1} ↦ (@IsAIC.exists_pow_eq _ _ _ _ ⟨by aesop⟩
    (algebraMap K Ω π)).imp fun _ h ↦ And.intro h (ne_zero_of_tame_root n.2 h)
  exact (isClosed_inertiaGroup.isCompact.inter_iInter_nonempty _ (fun n ↦ isClosed_setOf_smul (y n)
    ((IsPrimitiveRoot · n) ∘ (· / y n))) fun T ↦ (O ⟨T.prod (↑), by simp_all [T.prod_eq_one]⟩).rec
    fun Y ⟨_, n⟩ ↦ HasEnoughRootsOfUnity.prim.rec fun ζ hζ ↦ (G.exists_inertia_smul_eq_of_pow_eq u
    n.pos Y ((mul_pow ζ ..).trans (hζ.1 ▸ one_mul _))).rec fun s ⟨e, _⟩ ↦ ⟨s,
    e, by simp_all [fun p h ↦ show s.1 _ = _ from smul_root_eq_ratio_mul e p.2 (by rwa [← pow_mul,
    T.prod_erase_mul _ h]) (O p).1, mul_pow, hζ.pow n.pos, T.prod_erase_mul]⟩).elim fun g ⟨H, _⟩ ↦
    ⟨⟨g, H⟩, (⟨π, y ⟨·, ·⟩, by simp_all [h.isUniformiser_iff]⟩)⟩

/-- A chosen generator of tame inertia at the place A above w, as an element of the inertia
group. -/
noncomputable def tameGenerator := h.exists_tameGenerator.choose

/-- Let n be prime to w and f a homomorphism on Gal(Ω/K), trivial near 1 in inertia, with fⁿ = 1 on
inertia. For s in inertia, f(s) is a power of f at the chosen tame generator, and f(φsφ⁻¹) = f(s)^q
for a q-Frobenius φ. -/
lemma tame_inertia {P} [Monoid P] (f : Gal(Ω/K) →* P) (hf : ∀ᶠ g in nhds 1, g ∈ inertiaGroup _ A →
  f g = 1) {n : ℕ} (hn : A.valuation n = 1) (hP : ∀ g ∈ inertiaGroup _ A, f g ^ n = 1) (s :
  inertiaGroup Gal(Ω/K) A) : (∃ i, f s = f h.tameGenerator ^ i) ∧ ∀ q φ, IsFrob A q φ →
  f (φ * s * φ⁻¹) = f s ^ q := (h.exists_tameGenerator.choose_spec n hn).rec fun π ⟨y, u, e,
  p⟩ ↦ have H (g : inertiaGroup ..) := ((h.decompGroup_spec _).1.tame_inertia ((h.decompGroup_spec
    _).2.2 u) hn e ((f.domRestrict _).domRestrict _) (isOpen_of_mem_nhds _ ((nhds _).3
  (continuous_subtype_val.subtype_val.tendsto 1 hf) (by aesop_cat))) (by bound)).2 ⟨⟨_, g.2.1⟩, g.2⟩
  ⟨(H _).1 p ⟨⟨_, s.2.1⟩, s.2⟩, fun q φ a ↦ ((H s).2 q ⟨φ, a.1⟩ a).2⟩

/-- For A above w, there is a unit u of K_w whose local Artin image is the class of the chosen tame
generator of inertia and whose residue generates the multiplicative group of the residue field. -/
lemma exists_localArtin_eq_tameGenerator : ∃ u a, localArtin _ A w u = ⟦⟨_, h.tameGenerator.2.1⟩⟧ ∧
  (∀ z, z ∈ zpowers ((LocInt w).unitGroupToResidueFieldUnits ⟨u, a⟩)) ∧ v u.1 = 1 := by
  have ⟨g, hg, e⟩ := h.exists_localArtin_eq (inv_mem h.tameGenerator.2) 0
  have ⟨π, y, u, Y, p⟩ := h.exists_tameGenerator.choose_spec (w.q - 1) ?N
  use g, (mem_unitGroup_iff ..).2 hg, e, (eq_top_iff' _).1 (eq_top_of_le_card _ (by
    erw [Nat.card_zpowers, Nat.card_units, card_ResField]
    exact let r := _; Nat.le_of_dvd (orderOf_pos r) (p.2 _ ((eq_of_val_sub_lt_one ?N (by rw
        [pow_right_comm, p.1, one_pow]) (by simp [exp_neg, -inv_exp])
        (inertia_pow_smul_div h.tameGenerator.2 ?N Y _ ▸ (h.localArtin_tame_symbol u
      (by aesop) (e ▸ map_pow ..) Y).1 (residue_eq_iff_valuation_sub_lt_one.1 (val_inj.2
      (pow_orderOf_eq_one r))))).trans (map_one _))))), hg
  simp [map_sub_eq_of_lt_right, h.valuation_q_lt_one]
