/- GID: D5/S3/Zeros/GRH/Lib/ClassField/Global/Avatars
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/Global/Avatars
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.Global.Avatars. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/Global/Avatars.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.Chebotarev.FrobeniusFilter
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Global class field theory: Albert–Brauer–Hasse–Noether, reciprocity, existence, norms
(known result; see Lib.ClassField.Global.AlbertBrauerHasseNoether).

This file: Existence theorem of class field theory for totally complex fields, by Kummer counting.
p-adic avatar of algebraic Hecke characters over totally complex fields; values off p. -/

open Function Nat Set QZChar Fact Fint NumberField Pi QZ QuotientGroup Subgroup DiscreteUnits

variable {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [NumberField K] (n : ℕ) [NeZero n]
  (S :
  Set (FinPlace K)) {L M} [Field L] [NumberField L] [Algebra K L] [Field M] [NumberField M] (n' : ℕ)

@[simp] lemma adeleNorm_adeleNorm [Algebra K M] [Algebra L M] [IsScalarTower K L M] :
    ∀ y, adeleNorm K L (adeleNorm L M y) = adeleNorm K M y :=
  denseRange_algebraMap_finAdele.eq (by simp [Algebra.norm_norm])

/-- The group of finite ideles of K whose component at every place v in S is an n-th power in
K_v^×. -/
noncomputable abbrev idelesPowAt := ⨅ v : S, (powMonoidHom n').range.comap (ideleAt v.1)

lemma index_range_pow_eq {Y} [CommGroup Y] {n t : ℕ} (h : let q := cokerKerIndex (n : Module.End ℤ
    (Additive Y)); q ≠ 0 ∧ q = t) : let f := @powMonoidHom Y _ n; f.range.index ≠ 0 ∧ f.range.index
    = t * .card f.ker := (div_ne_zero_iff.1 h.1).imp (by tauto) (mod_cast div_eq_iff · |>.1 h.2)

/-- For n ≠ 0 the n-th powers have finite index in K_v^×, at most n²/|n|_v, that is n² times the
norm of the v-part of the ideal (n). -/
lemma index_pow_local_le (v : FinPlace K) : let i :=
    (@powMonoidHom (LocField v)ˣ _ n).range.index; i ≠ 0 ∧ i ≤ n ^
    2 * (v.1 ^ multiplicity v.1 (.span {↑n})).absNorm := let := (Ω.fieldEmb K).toAlgebra
  (v.isPlaceOver_placeOver.exists_isCompletionEmb Gal(Ω/K)).rec fun _ ⟨_, _, _, ⟨F⟩⟩ ↦ by
             rw [map_pow, ← FinPlace.q, ← F.residueCard_eq,
               ← (F.isUniformiser_iff.2 (v_uniformizer _)).card_quot F.2 _, sq, mul_right_comm]
             exact (index_range_pow_eq (mod_cast cokerKerIndex_local_units F.2 _ 0)).imp_right
               (·.trans_le (mul_right_mono (card_rootsOfUnity ..)))
             erw [← map_pow, ← map_pow,
               ((Valuation.isEquiv_iff_valuationSubring ..).2 F.valRingBelow_eq).eq_iff]
             simpa [v.intValuation_eq_exp_neg_multiplicity, NeZero.ne] using
               @v_algebraMap_eq_intValuation K _ _ v n

/-- For n ≠ 0 and a finite set S of finite places, the finite ideles that are n-th powers at all
places of S have finite index, at most n^(2|S| + [K:ℚ]). -/
lemma index_pow_at_places_le [Fintype S] :
  (idelesPowAt S n).index ≠ 0 ∧ (idelesPowAt S n).index ≤ n ^ (2 * S.ncard + Module.finrank ℚ K) :=
  have l v := index_comap_of_surjective _ (⟨_, @ideleAt_locIdele K _ _ v ·⟩) ▸ index_pow_local_le ..
  ⟨index_iInf_ne_zero (l · |>.1), by grw [index_iInf_le, (l _).2, Finset.prod_mul_distrib,
    ← map_prod, le_of_dvd _ (map_dvd _ (Fintype.prod_dvd_of_coprime (fun (v : S) _
    _ ↦ (v.1.isCoprime_of_ne _ (by lia)).pow) (pow_multiplicity_dvd ·.1.1 _)))] <;>
    simp [↓Ideal.absNorm_span_natCast, RingOfIntegers.rank, pow_add, pow_mul, NeZero.pos]⟩

variable [Algebra K Ω] [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω] {C} [Group C]
  [TopologicalSpace C]

/-- Let χ kill all complex conjugations, the inertia groups off S, and let nχ kill the
decomposition groups at S. Then χ∘Art kills the principal finite ideles and the ideles that
are n-th powers at S and units off S. -/
lemma QZChar.sup_le_ker_abelianLift_artinMap n χ (hc : ∀ {c}, IsComplexConj c → χ.1 c = 0) (h :
  ∀ w ∈ S, ∀ g ∈ decompGroup Γ (placeOver w), n • χ.1 g = 0) (h' : ∀ w ∉ S,
  ∀ g ∈ inertiaGroup Γ (placeOver w), χ.1 g = 0) : principalIdele.range ⊔ idelesPowAt S n ⊓
  idelesUnitOff S ≤ (abelianLift χ).ker.comap (artinMap Γ) :=
  sup_le (range_subset_iff.2 (char_artinMap_principalIdele_eq_one _ · @hc)) fun _ a ↦
  .trans (abelianLift_artinMap_eq_finprod ..) (finprod_eq_one_of_forall_eq_one fun v ↦ by_cases
  (mem_iInf.1 a.1 ⟨_, ·⟩ |>.choose_spec ▸ (map_pow ((abelianLift χ).comp _) ..).trans
  (((v.isPlaceOver_placeOver.range_abelianLift_artinAt χ).le ⟨_, rfl⟩).elim fun _ ⟨k, e⟩ ↦ e ▸ h _
  ‹_› _ k)) ((v.isPlaceOver_placeOver.artinAt_units_trivial_iff_unramified χ).2 (h' _ ‹_›) _ <|
  mem_idelesUnitOff.1 a.2 _ ·))

/-- Let K^× and the ideles that are units outside S generate the finite ideles. A continuous
homomorphism from Γ to a discrete abelian group killing complex conjugations, the chosen
decomposition groups over S and inertia groups outside S is zero. -/
lemma QZChar.eq_zero_of_unramified_off (hd : principalIdele.range ⊔ idelesUnitOff S = ⊤) {V}
  [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] (z : Z1 (.trivial ℤ Γ V)) (hc : ∀ c,
  IsComplexConj c → z.1 c = 0) (h : ∀ w ∈ S, ∀ g ∈ decompGroup Γ (placeOver w), z.1 g = 0) (h' :
  ∀ w ∉ S, ∀ g ∈ inertiaGroup Γ (placeOver w), z.1 g = 0) g : z.1 g =
  0 := eq_zero_of_forall_hom_eq_zero fun u ↦ congr(abelianLift (pairMapZ1 (.id _) u.toIntLinearMap
  (by simp) z) $((artinMap_surjective Γ g).choose_spec)).symm.trans
  (by apply sup_le_ker_abelianLift_artinMap S 1 <;> simp_all [inf_of_le_right, LE.le] <;> grind)

/-- Let nχ = 0, χ(Art x) = 0, χ unramified at distinct w_j with Frobenii φ_j. At each other v
let χ(Art_v x) = 0, or χ be unramified and x/r^n a unit for some inertia-fixed r ∈ Ω^×. Then
∑_j ord_{w_j}(x)χ(φ_j) = 0. -/
lemma sum_ord_smul_frob_eq_zero {n : ℕ} {χ} (hn : n • χ = 0) {x} (hc : abelianLift χ
  (artinMap Γ (principalIdele x)) = 1) {J} [Fintype J] {w} (i : @Injective J (FinPlace K) w) {A :
  J → ClosurePlace} {s : J → Γ} (hA : ∀ j, IsPlaceOver (A j) (w j) ∧
  IsFrob (A j) (w j).q (s j) ∧ inertiaGroup Γ (A j) ≤ ker χ) (h : ∀ v ∉ range w,
  let B := placeOver v; abelianLift χ (artinAt Γ v (ideleAt v (principalIdele x))) = 1 ∨ (∃ r, B
    ((ofBase Γ Ω (.ofMul x)).1 - n • r).toMul.1 = 1 ∧ ∀ g ∈ inertiaGroup Γ B, unitsRep g r = r) ∧
    inertiaGroup Γ B ≤ ker χ) : ∑ j, -((w j).valuation K x).log • χ.1 (s j) = 0 := by
  rw [abelianLift_artinMap_eq_finprod,
    finprod_eq_prod_of_mulSupport_subset _ (mulSupport_subset_iff'.2 fun v _ ↦
    (h v (by aesop)).rec id fun ⟨⟨_, a, h⟩, c⟩ ↦ ?_) (s := .map ⟨w, i⟩ ⊤)] at hc
  simp_all [(hA _).1.abelianLift_artinAt_of_unramified χ (hA _).2.2 (hA _).2.1, ← toAdd_eq_zero]
  obtain ⟨⟨k, e⟩, _, F⟩ := v.isPlaceOver_placeOver.ordRat_int_of_inertia_fixed h,
    v.isPlaceOver_placeOver.exists_isFrob Γ
  simp [↓← v.isPlaceOver_placeOver.ordRat_eq_zero_iff, e,
    v.isPlaceOver_placeOver.ordRat_ofBase] at a
  norm_cast at a
  simpa [v.isPlaceOver_placeOver.abelianLift_artinAt_of_unramified _ c F, mul_zsmul',
    a] using! congr(k • $hn.1 _)

/-- Let A lie over v, x ∈ K^× be an n-th power in K_v, and r^n = x. Every g in the decomposition
group of A that fixes the n-th roots of unity fixes r. -/
lemma IsPlaceOver.smul_root_eq_of_local_pow {n : ℕ} [NeZero n] {A : ClosurePlace} {v : FinPlace K}
  (h : IsPlaceOver A v) {x} (z : ideleAt v (principalIdele x) ∈ (powMonoidHom n).range) {r} (R : r ^
  n = algebraMap K Ω x) g (hg : g ∈ decompGroup Γ A) (e : cycCharMod Ω n g = 1) : g • r = r := by
  obtain ⟨⟨z, a⟩, _, _, _, j, ⟨F⟩⟩ := z, h.exists_isCompletionEmb Γ
  erw [cycCharMod_eq_of_equivariant (F.equivariant ⟨g, hg⟩), ← Units.val_eq_one, ← cast_one,
    cycCharMod_eq_iff] at e
  simpa [smul_div₀', ← F.equivariant, j.injective.eq_iff] using e (j r / algebraMap _ _ z.1)
    (by simpa [div_pow, ← map_pow, R, F.map_algebraMap, field] using! congr($a.1).symm)

/-- Let ζ ∈ μ_n ⊂ K be primitive. Kummer characters κ_x, ζ^{κ_x(g)} = ga/a for a^n = x, exist;
for K totally complex, finite S ⊃ {v ∣ n} generating the class group, an idele killed by all
κ_u∘Art (u an S-unit) is principal times one that is an n-th power at S, a unit elsewhere. -/
lemma exists_kummer_chars {n : ℕ} [NeZero n] (e : ∀ g : Γ, cycCharMod Ω n g = 1) : ∃ κ : _ →+ _,
  (∀ x a, n • a = ↑x → ∀ g, (rootPowHom Ω n).1 ((κ x).1 g) = unitsRep g a - a) ∧ ∀ [IsTotallyComplex
  K] {S}, S.Finite → principalIdele.range ⊔ idelesUnitOff S = ⊤ → (∀ v, ↑n ∈ v.1 → v ∈ S) → ∀ a,
  (∀ u : S.unit K, abelianLift (ofZModCocycle n (κ (ofBase Γ Ω (.ofMul u.1)))) (artinMap Γ a) = 1) →
  a ∈ principalIdele.range ⊔ idelesPowAt S n ⊓ idelesUnitOff S := by
  obtain ⟨i, z⟩ := (rootPowHom Ω n).2.1, isPrimitiveRoot_rootPowHom_one Ω n
  choose r κ R H using exists_kummer_cocycle e
  let κ := AddMonoidHom.mk' κ fun x z ↦ by
    ext; simp [← i.eq_iff, R, H _ (r _), H _ (r x + r z)]; abel
  use κ, H, @fun _ S f hd hS a ha ↦ ?_
  let o (u : S.unit K) := ofBase Γ Ω (.ofMul u.1)
  have F x g := (H _ _ (R x) g ▸ map_eq_zero_iff _ i (x := (κ x).1 g)).symm.trans sub_eq_zero
  obtain ⟨I, _, _, rk⟩ := fun u (v : FinPlace K) hv g hg ↦ (F (o u) g).2
    (ext (inertia_fixes_root_of_unit hg (v.isPlaceOver_placeOver.valuation_natCast_eq_one_iff.2
    (by tauto)) congr($(R _).1) (v.isPlaceOver_placeOver.valuationVia_eq_one_iff.2 (u.2 v hv))
    (smul_algebraMap ..))), f.fintype, SUnit.dirichlet_unit_theorem f
  have Y {u} : ∀ r, n • r = o u → u ∈ (· ^ n) '' o ⁻¹' {r} := (ofBase_bijective ..).2.forall.2 fun x
    t ↦ by obtain ⟨⟨_, h⟩, ⟨⟩⟩ := u, (ofBase_bijective ..).1 ((map_nsmul ..).trans t)
           exact ⟨⟨x, (by simpa [NeZero.ne] using! h · ·)⟩, rfl, rfl⟩
  have P u h := (Y ⟨_, (forall_congr' (F (o u))).1 h⟩ (Subtype.ext (R _))).imp fun _ ↦ (·.2)
  obtain ⟨q, p, x, hx, k⟩ := index_pow_at_places_le n S,
    @index_range_pow_eq (S.unit K) _ n _ (mod_cast cokerKerIndex_eq_pow_finrank), @Y 1
    ⟨_, (cycCharMod_eq_one_iff.1 · _ z.1) ∘' e⟩ (Subtype.ext (z.1.trans (by aesop)))
  have d := mem_divisors.2 ⟨(mul_dvd_mul_right (index_dvd_of_le (K := (powMonoidHom n).range) fun u
    h ↦ by apply P u (eq_zero_of_unramified_off S hd _ (nomatch ·, ·.false_of_isTotallyComplex)
    (fun v t g k ↦ (F ..).2 (ext (v.isPlaceOver_placeOver.smul_root_eq_of_local_pow
    (mem_iInf.1 h ⟨_, t⟩) congr($(R (o u)).1) g k (e g)))) (I u))) _).trans (relIndex_mul_index_sup
    hd principalIdele_mem_idelesUnitOff ▸ relIndex_dvd_index_of_normal ..), q.1⟩
  have := FiniteIndex.mk (right_ne_zero_of_mul (pos_of_mem_divisors d).ne')
  exact (eq_one_iff a).1 (eq_zero_of_forall_hom_eq_zero ((Injective.bijective_of_nat_card_le (f :=
    fun q ↦ (lift _ ((abelianLift _).comp _) (sup_le_ker_abelianLift_artinMap S n
    (ofZModCocycle n (κ (o q.out))) (·.false_of_isTotallyComplex.rec) (by simp [← map_nsmul])
    (by simp_all [I _ ·]))).toAdditiveLeft) (fun _ _ E ↦ Quotient.out_equiv_out.1 (leftRel_apply.2
    (P _ (artinMap_surjective Γ · |>.elim fun y ↦
    (by simpa [·, neg_add_eq_zero, o, ofZMod_injective.eq_iff] using congr($E <| .ofMul y))))))
    ((card_hom_QZ _).trans_le (le_of_mul_le_mul_left (((divisor_le d).trans
    (by grw [q.2, p.2, ← le_of_dvd (by lia) (z.2 (.card _) (by simpa [o, ← hx.symm] using! congr((o
    ($(@pow_card_eq_one' (powMonoidHom n).ker _ ⟨_, k⟩)).1).1))), ← pow_succ, rk]; simp [← pow_mul,
    ← InfinitePlace.sum_mult_eq]; lia)).trans_eq (sq _)) p.1.bot_lt))).2.forall.2 (ha ·.out)))

variable (Γ)

/-- Existence theorem: for K totally complex, a continuous homomorphism θ from the finite ideles
to a group C with a T₁ topology, trivial on K^×, is μ∘Art for a continuous homomorphism μ: Γ
→ C. -/
lemma exists_comp_artinMap [IsTotallyComplex K] [T1Space C] (θ : _ →* C) (h : Continuous θ) (h' :
  ∀ x, θ (principalIdele x) = 1) : ∃ μ : Γ →* C, Continuous μ ∧ ∀ x (g : Γ), artinMap Γ x = g →
  μ g = θ x := by
  have s := artinMap_surjective Γ
  refine (((artinMap Γ).liftOfSurjective s).symm.surjective ⟨θ, fun a ha ↦ by_contra ((ker_mk' θ.ker
    ▸ exists_apply_ne_zero_of_notMem_ker _ a) ⟨h.1 {1}ᶜ (by simp)⟩ · |>.elim fun ψ H ↦
    H.2 ?_)⟩).rec ?_
  rintro μ ⟨⟩
  use μ.comp (mk' _), ((((artinMap Γ).isOpenMap_of_sigmaCompact s continuous_artinMap).isQuotientMap
    continuous_artinMap s).continuous_iff.2 h).comp continuous_mk, by aesop
  obtain ⟨h, _, hr⟩ := (H.1 _ <| h' ·), NeZero.mk (finiteIndex_idele_subgroup_of_isOpen (ker ψ) out
    (by tauto)).1, by simpa using (ker ψ).pow_index_mem
  generalize (ker ψ).index = n at *
  clear! θ s
  induction' e : @index Γ _ (cycCharMod Ω n).ker using Nat.strongRec with _ ih generalizing Γ K
  obtain ⟨E | ⟨g, χ, f⟩, _, t⟩ := (@forall_or_exists_not Γ _).imp_right
    (·.imp (exists_apply_ne_zero_of_notMem_ker (cycCharMod Ω n) · inferInstance)),
    exists_sup_idelesUnitOff_eq_top ((finite_natCast_mem n).union
    (eventually_unramified (toHom ψ) out))
  exact sup_le (c := ker ψ) (by aesop_cat) (fun _ d ↦ mem_of_locIdele_mem (H :=
    ker ψ) ⟨ψ.2.1.1 {0}ᶜ ⟨⟩⟩ fun v ↦ by_cases (mem_iInf.1 d.1 ⟨_, ·⟩ |>.choose_spec ▸ by simp [hr])
    (by_contra (t.2.1.mt ‹_› ∘ .inr) _ <| mem_idelesUnitOff.1 d.2 v ·))
    ((exists_kummer_chars E).choose_spec.2 t.1 (by tauto) (by tauto) a (by aesop))
  let U := ker χ
  obtain ⟨_, _, x, y, p, ⟨⟩⟩ := isTotallyComplex_of_algebra K (fixedFieldOf U),
    U.quotient_finite_of_isOpen out, (char_artinMap_eq_one_iff χ a).1 (by aesop)
  let ρ := comap ⟨_, (continuous_adeleNorm K (fixedFieldOf U)).units_map _⟩ ψ
  simpa [ψ.2.2, h] using! ((ker ρ).comap_map_eq_self (ih _ (e ▸ relIndex_mul_index (K := U) f.1 ▸
    lt_mul_of_one_lt_right card_pos (one_lt_index_of_ne_top (f.2 <| ·.ge ⟨⟩))) U · · ρ (by simp [ρ,
    QZChar.comap, map_adeleNorm_principalIdele, h]) (by tauto) rfl)).le (mem_comap.2
    ((artinMap U y).out_eq ▸ ((((ker ρ).map _).comap (mk' _)).mem_map_iff_mem U.subtype_injective).1
    (closure_minimal ((Normal.quotient_commutative_iff_commutator_le.1
    (((expUnit.comp (kerLift _)).rangeRestrict.comp
    (map _ _ (.id _) (commutator_le_left U ⊤))).isMulCommutative_of_isCyclic_of_ker_le_center
    (Quot.ind fun _ h ↦ (Subgroup.upperCentralSeriesStep_eq_comap_center _).le fun _ ↦
    commutator_mem_commutator (expUnit_eq_one_iff.1 congr($h)) ⟨⟩))).trans (commutator_le.2 fun k h
    g _ ↦ let := ((MulSemiringAction.toAlgHom K Ω g⁻¹).restrictNormal (fixedFieldOf U)).toAlgebra
    (artinMap_surjective U ⟦⟨k, h⟩⟧).elim fun y hy ↦ by exact ⟨_ / MulAut.conjNormal g ⟨k, h⟩,
      ⟨_, (toHom ρ).div_mem_ker_iff.2 congr(ψ.1 $(by bound)),
      (map_div ..).trans (congrArg₂ _ hy (artinMap_adeleNorm hy _ (AlgHom.restrictNormal_commutes _
      _ · |>.symm) (by simp [U.smul_def, mul_smul])))⟩, by simp [div_eq_mul_inv]; group⟩))
    (isClosed_of_isOpen _ (.trans ((artinMap U).isOpenMap_of_sigmaCompact
    (artinMap_surjective U) continuous_artinMap _ out) out)) ((eq_one_iff _).1 ((artinMap_adeleNorm
    (artinMap U y).out_eq.symm).symm.trans (by simp_all [artinMap_principalIdele]))))))

variable [IsTotallyComplex K] {K'} [Field K'] [EmbeddedNumberField K'] {p : ℕ} [Fact p.Prime]
  [PadicIso p] [IsTotallyComplex K'] (θ : AlgHeckeChar K')

/-- Let K be totally complex and let the ideles that are m-th powers at all places of S have
finite index I. Then some finitely many p_i in Γ and n_i ≥ 2 with ∏n_i ∣ h_K·I detect each
locally constant homomorphism x killed by m and unramified outside S: n_i x(p_i) = 0, and x
= 0 if all x(p_i) = 0. -/
lemma exists_detecting_points_hom m (h : (idelesPowAt S m).index ≠ 0) : ∃ (ι : Type) (_ :
  Fintype ι) (p n : ι → _), (∀ i, 2 ≤ n i) ∧ ∏ i, n i ∣ classNumber K * (idelesPowAt S m).index ∧
  ∀ {B} [AddCommGroup B] {x : Γ → B}, IsLocallyConstant x → (∀ g h, x (g * h) = x g + x h) →
  m • x = 0 → (∀ v ∉ S, ∀ g ∈ inertiaGroup Γ (placeOver v), x g = 0) → (∀ i, n i • x (p i) = 0) ∧
  ((∀ i, x (p i) = 0) → x = 0) := by
  have d : ((principalIdele.range ⊔ idelesPowAt S m ⊓ idelesUnitOff S).map (artinMap Γ)).index ∣
    classNumber K * (idelesPowAt S m).index := by grw [index_map_dvd, ← relIndex_mul_index,
    relIndex_sup_left, mul_comm, index_dvd_of_le (exists_idele_classGroup_hom.choose_spec.trans_le
    (sup_le_sup _ (idelesUnitOff_mono _))), relIndex_dvd_of_le_left _ le_sup_right, index_ker,
    inf_relIndex_right, relIndex_dvd_index_of_normal,
    card_subgroup_dvd_card] <;> simp [artinMap_surjective, classNumber]
  let ⟨ι, F, n, hn, ⟨ε⟩⟩ := @CommGroup.equiv_prod_multiplicative_zmod_of_finite _ _
    (finite_of_card_ne_zero (ne_zero_of_dvd_ne_zero (by simpa [classNumber]) d))
  let p i := (ε.symm (mulSingle i (.ofAdd 1))).out.out
  use ι, F, p, n, hn, by simp_all [index, card_congr ε.1, card_pi, Multiplicative], fun q _ _ _ ↦
    have H (f : _ →+ _) := (ker_mk' _).trans_le (map_le_iff_le_comap.2
      (sup_le_ker_abelianLift_artinMap S m ⟨_, (q.comp f).continuous, by simp [*]⟩
      (·.false_of_isTotallyComplex.rec) (by simp_all [← map_nsmul, funext_iff]) (by grind)))
    ⟨fun g ↦ eq_zero_of_forall_hom_eq_zero ?_, fun h ↦ funext fun g ↦
      eq_zero_of_forall_hom_eq_zero ?_⟩
  simpa using! (@H · (p g ^ n g) (ε.injective (by simp [p, ← mulSingle_pow]; aesop)))
  simpa [h] using fun f ↦ (@H f (QuotientGroup.mk g / ∏ i, QuotientGroup.mk (p i) ^
    (ε g i).toAdd.valMinAbs) :) (ε.injective (by ext; simp [p, mulSingle, update]))

/-- For K' totally complex and ι : ℂ ≅ Q̄_p, some homomorphism sends each algebraic Hecke character
(θ, n) to a continuous μ : Gal(Ω/K') → Q̄_p^× with μ(g) = ι(θ(x)) ∏_σ (ισ)(x_p)^{n_σ} whenever g has
image Art x in Gal(Ω/K')^ab.

Known result: ℓ-adic avatar of an algebraic Hecke character and its local behaviour. -/
lemma exists_avatar : ∃ av : AlgHeckeChar K' →* Gal(Ω/K') →* _ˣ, ∀ θ, Continuous (av θ) ∧ ∀ x g,
  artinMap _ x = ⟦g⟧
  → (av θ g).1 = ιℓ (θ.1.1 x) * ∏ σ, adeleExtension (ιℓ.toRingHom.comp σ) x ^ θ.1.2.toAdd σ := by
  choose μ h using fun θ : AlgHeckeChar K' ↦ exists_comp_artinMap Gal(Ω/K') ((Units.map ιℓ).comp
    θ.1.1 * ∏ σ, Units.map (adeleExtension (ιℓ.toRingHom.comp σ)).1 ^ θ.1.2.toAdd σ) (.mul
    (.of_isOpen_ker _ (isOpen_mono (by aesop_cat) θ.2.1)) (by
   eta_expand; simpa using continuous_finsetProd _ fun _ _ ↦ (continuous_adeleExtension
     _).units_map.zpow _)) (by
    simp [Units.ext_iff, θ.2.2, inv_mul_cancel₀, Finset.prod_ne_zero_iff, zpow_ne_zero])
  use .mk' μ fun a b ↦ by ext; simp [(h _).2 _ _ (artinMap_surjective ..).choose_spec,
    zpow_add, field], by simpa [Units.ext_iff] using h

/-- The p-adic avatar: a chosen homomorphism sending the algebraic Hecke character (θ, n) to the
continuous character μ of Gal(Ω/K') with μ(Art x) = ι(θ(x)) ∏_σ (ισ)(x_p)^{n_σ}. -/
noncomputable def AlgHeckeChar.avatar := exists_avatar (K' := K').choose

@[fun_prop] lemma AlgHeckeChar.continuous_avatar : Continuous (avatar θ) := by grind [avatar]

/-- Let A lie over v, with v ∤ p or n_σ = 0 whenever ιℓ∘σ induces v. If g in the decomposition
group D of A has class Art_v(x) in D^ab, the avatar of (θ, n) at g is ιℓ(θ(x)), x an idele
at v. -/
lemma AlgHeckeChar.avatar_localArtin {A v} (h : IsPlaceOver A v) (hv : ↑p ∉ v.1 ∨ ∀ σ, inducedPrime
  σ = v → θ.1.2.toAdd σ = 0) {x g} (hg : localArtin Gal(Ω/K') A v x = ⟦g⟧) : (avatar θ g).1 =
  ιℓ (θ.1.1 (locIdele v x)) := by erw [(exists_avatar.choose_spec θ).2 (locIdele v x),
  Finset.prod_eq_one fun σ _ ↦ by by_cases inducedPrime σ = v <;> subst_vars <;> simp_all
  [adeleExtension, -RingEquiv.toRingHom_eq_coe]] <;> simp [h.artinAt_eq_of_localArtin_eq hg]
