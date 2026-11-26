import GRH.Lib.ClassField.Global.AlbertBrauerHasseNoether
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Global class field theory: Albert–Brauer–Hasse–Noether, reciprocity, existence, norms
(known result; see Lib.ClassField.Global.AlbertBrauerHasseNoether).

This file: Artin reciprocity law on principal finite ideles, via cyclotomic characters; sign law. -/

open Nat Set QZChar IsCyclotomicExtension MulSemiringAction NumberField Polynomial QZ Valuation ZMod

variable {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [EmbeddedNumberField K]
  [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω]

/-- Artin reciprocity for K(μ_q), q an odd prime: some continuous character χ has the same
kernel as the cyclotomic character modulo q, and for x ∈ K^×, χ(Art x) = 0 exactly when
N_{K/ℚ} x > 0. -/
lemma artin_reciprocity_cyclotomic {q : ℕ} [P : Fact q.Prime] (hq : Fact (2 < q)) :
    ∃ χ, ker χ = (cycCharMod Ω q).ker ∧ ∀ x,
  abelianLift χ (artinMap Γ (principalIdele x)) = 1 ↔ 0 < Algebra.norm ℚ x.1 := by
  obtain ⟨⟨ξ, h⟩, ⟨v, ⟨⟨⟩, o⟩, π, -⟩, O, n, ζ, z⟩ := exists_ker_eq_of_isCyclic ⟨cycloGalGroup q,
    isOpen_ker_cycCharMod.1⟩ (isCyclic_of_injective _ (QuotientGroup.kerLift_injective _)),
    exists_rat_place_of_prime P.1, @FinPlace.isPlaceOver_placeOver ℚ, sub_ne_zero_of_lt hq.1.le,
    @HasEnoughRootsOfUnity.prim Ω _ q _
  let F := (abelianLift ξ).comp ((artinMap _).comp principalIdele)
  let A := placeOver v
  obtain ⟨⟨ε, e⟩, π, f⟩ := (Rat.associated_zeta_sub_one_pow_prime _ z).map ((algebraMap
    ..).codRestrict A (algebraMap_ringOfIntegers_mem A)), (O v).isUniformiser_iff.2 π,
    (O · |>.exists_isFrob Gal(Ω/ℚ) |>.choose_spec)
  let ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ε.1.1 n.bot_lt
  have T (k : ℤ) {g u} hu hx : abelianLift ξ (artinAt _ v u) = toHom ξ g ↔ k =
    (cycCharMod Ω v.q g).1 := ((O v).exists_inertia_eq_localArtin hu).rec fun s ⟨hs, E⟩ ↦
    ((O v).artinAt_eq_of_localArtin_eq E).substr (by
    erw [(toHom ξ).eq_iff, ← ker, h, ← (cycCharMod ..).eq_iff, Units.ext_iff, Eq.congr_left]
    simpa [← intCast_eq_intCast_iff_dvd_sub, ↓Algebra.norm_algebraMap, RingOfIntegers.rank] using
      (Ideal.absNorm_dvd_norm_of_mem ((O v (algebraMap ℤ _ (k - .ofNat _))).1 (by
      simpa [geom_sum_eq, z.ne_one hq.1.le, ← Finset.sum_mul, -natCast_val, mul_div_mul_comm,
      smul_sub, cycCharMod_spec s.1 z.1] using map_sub_lt _ (A.valuation.map_sum_lt' one_pos (s :=
      .range (cycCharMod Ω v.q s.1).1.val) fun i _ ↦ A.principalUnitGroup.mul_mem (pow_mem (x :=
      ↑z.toRootsOfUnity) ((pow_lt_one_iff n).1 (by simpa using congr(A $e.1).trans_lt π.val_lt_one))
        i) (y := .mk0 _ (by simpa [n] using congr( $hw = 0))) (valuation_smul_div_sub_one_lt_one hs
        (by simpa [n] using congr(A $hw))) :) (((O v).localArtin_tame_symbol π
      hu E (x := k) ((mul_pow (ζ - 1) w _).trans (hw ▸ congr($e.1)))).1 hx))) :))
  have u w := (O w).valuationVia_eq_one_iff.2 ∘ o w
  have V w n := (O w).abelianLift_artinAt_of_unramified ξ (h.ge <|
    cycCharMod_of_mem_inertiaGroup (σ := ·) · (u w n)) (f w)
  have S w y (a : ∀ u ≠ w, u.valuation ℚ y = 1) : F y = ∏ u ∈ {w, v}, _ :=
    (abelianLift_artinMap_eq_finprod ..
    ).trans (finprod_eq_prod_of_mulSupport_subset _ (by simp_all [not_imp_comm]))
  have N : ∀ (n : ℕ) h, F (.mk0 n h) = 1 := recOnMul nofun (by simp) (fun p r t ↦ ?_) (by simp_all)
  obtain ⟨w, ⟨⟨⟩, o'⟩, π⟩ := exists_rat_place_of_prime r
  obtain ⟨⟨⟨⟩⟩ | n, E⟩ := eq_or_ne w v, S w (.mk0 _ t) o'
  simpa [E] using abelianLift_artinAt_of_mem_closure (subset_closure (h ▸ ⟨_, congrArg _
    (norm_zeta_sub_one_of_prime_ne_two _ (cyclotomic.irreducible_rat r.pos) hq.1.ne')⟩))
  simpa [*, inv_mul_eq_iff_eq_mul] using! (T w.q (by erw [v_algebraMap_eq_valuation, o' v n.symm])
    (by simp [ideleAt])).2 (by simp [(f w).cycCharMod_eq (u w n)])
  have M y := by simpa [↓N, ↓F.map_mul, apply_ite, S v, ideleAt,
    principalIdele, by simpa [neg_one_ne_one]
    using (@T (-1) 1 (-1))] using congrArg (F · = 1) (show y * .mk0 y.1.den (by simp) = ite (0 <
    y.1) 1 (-1) * .mk0 y.1.num.natAbs (by simp) by ext; split <;> simp_all [abs, le_of_lt])
  use QZChar.comap ⟨toAlgAut .., continuous_of_equivariant_emb 1⟩ ξ, congrArg (Subgroup.comap _) h,
    fun x ↦ (artinMap Γ _).out_eq' ▸ congr(abelianLift ξ $((artinMap_adeleNorm (Quot.out_eq
    _).symm).symm.trans (congrArg _ (map_adeleNorm_principalIdele x)))).congr_left.trans (M _)

/-- Artin's reciprocity law: if the symbol (ξ, x), x ∈ K^×, restricts to zero on some open
subgroup containing all complex conjugations, then ξ kills the Artin image of the principal
finite idele of x. -/
lemma artin_reciprocity {ξ x} (U : OpenSubgroup Γ) (c : ∀ c, IsComplexConj c → c ∈ U)
    (e : (unitsModule Γ).resH2 U (cyclicClass _ ξ (DiscreteUnits.ofBase Γ Ω (.ofMul x))) = 0) :
  abelianLift ξ (artinMap Γ (principalIdele x)) = 1 := by
  choose σ hσ using fun v : FinPlace K ↦ v.isPlaceOver_placeOver.exists_isFrob Γ
  let n v := orderOf (abelianLift ξ (artinAt Γ v (ideleAt v (principalIdele x))))
  let H (i : Σ _, ℕ) := (Submodule.torsion' ℤ _ (Submonoid.mk ⟨i.2.Coprime, .mul_right⟩
    i.2.gcd_one_right)).toAddSubgroup.comap (.mk' (n i.1 • ·.1.1 (σ i.1) : (AddSubgroup.pi (range
    (artinMap Γ ∘ principalIdele)) ⊥).comap
    (.mk' (abelianLift · · |>.toAdd) (by intros; ext ⟨⟩; rfl)) → _) (by simp))
  refine (abelianLift_artinMap_eq_finprod ..).trans ((em' _).elim finprod_of_infinite_mulSupport
    fun s ↦ (nonempty_compl.2 ((@AddSubgroup.exists_finiteIndex_of_leftCoset_cover _ _ _ H 0
    (s.toFinset.sigma (primeFactors ∘ n))).mt fun ⟨⟨v, l⟩, hl, ⟨i⟩⟩ ↦ ?_)).elim fun χ f ↦
    (((cyclicClass_spec χ.1).1 _).1 (albert_brauer_hasse_noether _ (fun {A w} o ↦ ?_) (U.comap _
    (subgroupIncl _).2) (c ·) (DiscreteModule.resH2_swap (congrArg _ e) :))).elim fun y E ↦
    .trans (finprod_congr (have h := FinPlace.isPlaceOver_placeOver ·
    (h.decompGroup_spec Γ).1.isClassOfInv_classOfInv.1 (by erw [h.abelianLift_artinAt_principal, E,
      h.abelianLift_artinAt_principal])))
    ((abelianLift_artinMap_eq_finprod ..).symm.trans (χ.2 _ ⟨y, rfl⟩)))
  simp at hl
  obtain ⟨g, N, hl⟩ := one_lt_mul l.add_one_pos hl.2.1.one_lt,
    one_lt_pow (mul_ne_zero (mul_ne_zero two_ne_zero i) hl.2.2.2) v.one_lt_q, hl.2.1
  obtain ⟨q, p, d⟩ := exists_prime_and_dvd ((sub_one_lt_natAbs_cyclotomic_eval g
    N.ne').trans_le' (by omega)).ne'
  obtain ⟨_, _, o⟩ := Fact.mk p, NeZero.of_not_dvd (ZMod q) (not_dvd_ordCompl p g.ne_bot),
    ordCompl_pos q g.ne_bot
  have y := isRoot_cyclotomic_prime_pow_mul_iff_of_charP.1 ((cyclotomic.eval_apply _ _
    (algebraMap ℤ (ZMod q))).trans (by rwa [eq_intCast, intCast_zmod_eq_zero_iff_dvd,
    Int.natCast_dvd, ordProj_mul_ordCompl_eq_self]))
  have z := y.eq_orderOf ▸ orderOf_lt p.one_lt _
  have u := dvd_ordCompl_of_dvd_not_dvd (dvd_mul_left l l.succ) fun e ↦ (le_of_dvd hl.pos
    e).not_gt ((le_of_dvd o (dvd_ordCompl_of_dvd_not_dvd (dvd_mul_right ..)
    (by simpa [p.ne_one] using dvd_sub · e))).trans z.le)
  exact (artin_reciprocity_cyclotomic (q := q) ⟨by grw [hl.two_le, le_of_dvd o u, z]⟩).elim
    fun χ ⟨E, A⟩ ↦ ((H ⟨v, l⟩).nsmul_index_mem ⟨χ + χ, fun _ ⟨x, k⟩ ↦ k ▸ by
    simpa [map_add] using! A (x * x)⟩).elim fun m _ ↦ hl.coprime_iff_not_dvd.1 m.2 (u.trans
    (y.2 _ (by simpa [Units.ext_iff, (hσ v).cycCharMod_eq (((isUnit_iff_coprime _ q).1 (by
    simpa [*] using y.isUnit o.ne')).valuation_eq_one v.isPlaceOver_placeOver.valuation_q_lt_one)]
    using (E.le (by simpa [pow_mul, sq] : (σ v ^ _) ^ m.1 ∈ _)))))
  refine (unitsModule ..).resH2_swap (V := decompGroup ..) <| (LinearMap.ker _).neg_mem_iff.1
    ((o.isPlaceOver_below.abelianLift_artinAt_principal ..).subst
    ((o.isPlaceOver_below.decompGroup_spec Γ).1.resH2_classOfInv_eq_zero
    ⟨_, (isOpen_ker _).preimage_val⟩ (addOrderOf_dvd_iff_nsmul_eq_zero.1 ?_)))
  have ⟨b, a, c, hb, d⟩ := (n (w.below K)).exists_coprime ((ker χ.1).relIndex (decompGroup Γ A))
  exact by_contra fun h ↦ f (mem_iUnion₂.2 ⟨⟨_, b.minFac⟩, by simpa [n] using ⟨(h <| by simp [·]),
    (h <| by simpa [·, gcd_eq_left_iff_dvd] using! hb.symm), b.minFac_dvd.trans ⟨_, hb⟩,
    isAddTorsion _⟩, _,
    ⟨⟨a, c.of_dvd_left b.minFac_dvd⟩, (smul_smul a ..).trans (orderOf_dvd_iff_pow_eq_one.1
    ((Subgroup.orderOf_dvd_natCard _ (((FinPlace.isPlaceOver_placeOver _).range_abelianLift_artinAt
    _).ge ⟨_, (hσ _).1, rfl⟩)).trans (by grw [o.isPlaceOver_below.range_abelianLift_artinAt,
    ← Subgroup.relIndex_ker, d, gcd_dvd_left])))⟩, by simp⟩)

/-- Artin reciprocity: if χ kills all complex conjugations, then χ kills the Artin image of the
principal finite idele of every x ∈ K^×.

Known result: Global class field theory: Albert–Brauer–Hasse–Noether, reciprocity, existence,
norms. -/
lemma char_artinMap_principalIdele_eq_one χ x (h : ∀ c, IsComplexConj c → χ.1 c = 0) :
    abelianLift χ (artinMap Γ (principalIdele x)) = 1 :=
  artin_reciprocity _ h (((cyclicClass_spec χ).1 _).2 ⟨x, rfl⟩)

/-- The global Artin map kills the principal finite idele of every totally positive x ∈ K^×. -/
lemma artinMap_principalIdele {x} (h : IsTotallyPositive x.1) :
    artinMap Γ (principalIdele x) = 1 := abelianization_ext fun _ ↦
  (h.exists_resH2_cyclicClass_eq_zero.choose_spec.elim (artin_reciprocity _)).trans (by simp)

/-- Sign law: let K be a number field and χ a continuous character of its Galois group Γ
non-trivial on every complex conjugation in Γ. Then for b in K^×, χ(Art b) is trivial
exactly when the norm of b to ℚ is positive. -/
lemma char_artinMap_principalIdele_eq_one_iff {χ} (h : ∀ c, IsComplexConj c → χ.1 c ≠ 0) b :
  abelianLift χ (artinMap Γ (principalIdele b)) = 1 ↔ 0 < Algebra.norm ℚ b.1 :=
  (artin_reciprocity_cyclotomic ⟨.refl⟩).elim fun ξ ⟨e, l⟩ ↦ (div_eq_one.1 (.trans (by
  rcases artinMap _ _; rfl) (char_artinMap_principalIdele_eq_one (χ - ξ) b fun c g ↦ sub_eq_zero.2 (
  have k χ := (Fin.exists_fin_two.1 (exists_ofZMod ((two_nsmul _).trans (map_mul_eq_one (toHom χ)
  g.mul_self)))).resolve_left ∘ (map_zero _).trans_ne ∘ .symm
  (k _ (h c g)).symm.trans (k _ (nomatch g.cycCharMod_eq_neg_one.symm.trans <|
    e.le ·)))))).congr_left.trans (l b)
