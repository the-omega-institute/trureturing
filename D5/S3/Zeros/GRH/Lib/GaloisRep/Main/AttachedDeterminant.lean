/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/Main/AttachedDeterminant
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/Main/AttachedDeterminant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.Main.AttachedDeterminant. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/Main/AttachedDeterminant.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.Characters.LocalCharacters
import D5.S3.Zeros.GRH.Lib.ClassField.Grunwald.Grunwald
import D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange.BaseChangeEigenchar
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.PairSumNegation
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Grunwald–Wang theorem in prime exponent. It is proved here for prime exponent over
a totally complex field, and the character also agrees with the given one on units at all primes of
degree above one. A CM extension of prime degree with prescribed tame completion at a split place
follows. Source: Artin–Tate, Class Field Theory (1968), ch. X; S. Wang, Grunwald–Wang theorem, an
effective version, arXiv 1401.0389 (2014).

Part of: Galois representations attached to forms on definite unitary groups (known result; see
Lib.GaloisRep.Main.AvatarCompatibility).

This file: Field cut out by χχ^c is CM of prime degree, with norm-detecting character. CM extension
of prime degree with prescribed tame completion at a split place. Auxiliary quadratic CM extension
containing imaginary quadratic field, split at given places. Local properties descend from the
base-changed form's representation to the original one. Determinant of an attached Galois
representation is the avatar of the twisted central character. -/

section

open NumberField Ideal Algebra ComplexEmbedding Subgroup QZChar QZ FractionalIdeal RingOfIntegers
section
variable {E} [Field E] [EmbeddedNumberField E] [IsCMField E] (χ : QZChar Gal(Ω/E))

/-- The extension of the CM field E inside Ω cut out by the character g ↦ χ(g) + χ(g^c), that
is, the fixed field of its kernel. -/
noncomputable abbrev QZChar.stepField := fixedFieldOf (ker (symmetrise χ))

instance : IsCMField (stepField χ) := isCMField_of_forall_exists_conj E fun y ↦ ⟨⟨_, (cmConj_cmConj
  _ ▸ congr(cmConj $(y.2 ⟨_, add_eq_zero_symm <| congr(χ.1 $(conjGal_conjGal _) + _).trans ·.2⟩)))⟩,
  (lift_comp_algebraMap Ω · ▸ let J := lift Ω _; (exists_smul_emb_eq _ (J.comp cmConj) (star J) (by
    ext; simpa using map_star_complex (J.comp _) _)).rec fun g h ↦ (y.2 ⟨g, map_mul_eq_one (toHom χ)
    (mul_eq_one_symm (by ext; simp_all [← J.injective.eq_iff, conjGal]))⟩ ▸ h y :))⟩

end

open InfinitePlace in noncomputable instance {E} [Field E] [EmbeddedNumberField E] [CMType E]
    (χ : QZChar Gal(Ω/E)) : CMOver E (stepField χ) where
  Φ u := let e := u.embedding
    ite (e.comp (algebraMap ..) = Φ (u.comap (algebraMap E _))) e (star e)
  mk_Φ := by aesop
  mem_type_iff := by grind [embedding_mk_eq, Φ_eq_or, comap_mk, conjugate_comp, star_star]

variable {E} [Field E] [EmbeddedNumberField E] [IsCMField E] (χ : QZChar Gal(Ω/E))

instance [h : StablyUnram E] : StablyUnram (stepField χ) :=
  ⟨_, h.1.choose_spec.map_of_injective (algebraMap ..).injective⟩

/-- Let E' be the field cut out by g ↦ χ(g) + χ(g^c) and u a prime of E'. If this character
kills the inertia groups above the prime of E below u, then u does not divide the different
of E' over E. -/
lemma QZChar.not_dvd_differentIdeal_stepField {u : FinPlace (stepField χ)} (h :
  ∀ {A : ClosurePlace}, IsPlaceOver A (u.below E) → inertiaGroup _ A ≤ ker (symmetrise χ)) :
  ¬u.1 ∣ differentIdeal (𝓞 E) _ := not_dvd_differentIdeal_iff.2 <|
  ramificationIdx_eq_one_iff.1 ((u.isPlaceOver_placeOver.isPlaceOver_below.ramification_in_tower _
  u.isPlaceOver_placeOver).2.1 (h u.isPlaceOver_placeOver.isPlaceOver_below))

/-- Let E be stably unramified CM, p prime, pχ = 0, and ξ(g) = χ(g) + χ(g^c) non-zero and
unramified above p. Then the field of ξ has degree p over E and forms a step (`IsStep`)
with the character exp(2πi χ∘Art). -/
lemma isStep_stepField [StablyUnram E] {p} (hp : Nat.Prime p) (h : p • χ = 0) {g₀} (h₀ :
  (symmetrise χ).1 g₀ ≠ 0) (ht : ∀ {A : ClosurePlace} {u : FinPlace E}, IsPlaceOver A u → ↑p ∈ u.1 →
  inertiaGroup _ A ≤ ker (symmetrise χ)) :
  IsStep (stepField χ) (ideleChar χ) ∧ Module.finrank E (stepField χ) = p := have := Fact.mk hp
  (iff_and_self.2 fun | rfl => ⟨isOpen_mono (expUnit.ker.ker_le_comap _)
    (continuous_iff_isOpen_ker.1 continuous_artinMap χ), by simp [artinMap_principalIdele,
    isTotallyPositive_of_isTotallyComplex], by simp [isTotallyPositive_of_isTotallyComplex,
    ← abelianLift_symmetrise, char_artinMap_eq_one_iff (symmetrise χ), expUnit_eq_one_iff],
    ((eq_top_iff_one _).1 ((IsDedekindDomain.HeightOneSpectrum.ideal_ne_top_iff_exists
    (not_isField E) (intTrace ..).range).not_right.2 fun ⟨u, hI⟩ ↦ by
    obtain ⟨n, P, ⟨⟩⟩ := coeIdeal_ne_zero (K := E).2 u.3,
      FinPlace.comap_surjective (algebraMap E (stepField χ)) u
    refine not_dvd_differentIdeal_stepField χ (ht · (hI ⟨1, ext ?_⟩)) <| dvd_iff_le.2 <|
      (differentialIdeal_le_iff (L := stepField χ)
      ?_).2 fun _ ⟨x, hx⟩ ↦ coe_one.le <| (div_self n).le <| (mem_div_iff_of_ne_zero n).2 fun
      | _, ⟨a, ha, rfl⟩ => ((mem_inv_iff ?_).1 hx.1 _ ⟨_, ha, rfl⟩).rec fun z _ ↦ ⟨_, hI ⟨z, rfl⟩,
      ?_⟩ <;> simp_all [algebraMap_intTrace (L := stepField χ), algebraMap_eq_smul_one, trace_apply,
      map_one, P.3])).imp (by simp [← algebraMap_intTrace (A := 𝓞 E)])⟩).1 (by
    rw [finrank_fixedFieldOf, eq_comm, ← hp.dvd_iff_eq (h₀ <| index_eq_one.1 · |>.ge ⟨⟩), index_ker]
    exact .trans (card_dvd_of_le fun | _, ⟨_, rfl⟩ => χ.2.2 .. ▸ exists_ofZMod congr($h.1 _))
      (p.card_zmod ▸ card_range_dvd (ofZMod p).toMultiplicative))

/-- Grunwald: for E with Weil data, w split and χ ≠ 1 a tame character of E_w^× killed by the
prime p, some ν trivial at w gives a degree-p step E' with Weil data and one place above w,
split, where ννᶜ corresponds to χ at w.

Known result: Grunwald–Wang theorem in prime exponent. -/
lemma exists_step_of_local_char {E} [Field E] [EmbeddedNumberField E] [CMType E] {w :
  FinPlace E} {A : ClosurePlace} [WeilData E] {p} (hw : w.IsSplit) (hA : IsPlaceOver A w) (hp :
  p.Prime) (χ : _ →* _) {x₀} (h₁ : χ x₀ ≠ 1) (hχ : ∀ x, χ x ^ p = 1) (ht : ∀ x, Valued.v x.1 = 1 →
  χ (x ^ (w.q - 1)) = 1) : ∃ ν : QZChar Gal(Ω/E), let E' := QZChar.stepField ν; ∃ (u : FinPlace E')
    (_ : WeilData E'), IsStep E' (QZChar.ideleChar ν) ∧ Module.finrank E E' = p ∧ u.IsSplit ∧ (∀ u',
    u'.below E = w ↔ u' = u) ∧ IsPlaceOver A u ∧ (∀ x, QZChar.abelianLift ν (artinAt _ w x) = 1) ∧
    ∀ x, QZChar.abelianLift (QZChar.symmetrise ν) (artinAt _ w x) = χ x := by
  obtain ⟨_, ν, hν, h⟩ := Fact.mk hp, grunwald hp (((@finite_natCast_mem _ _ _ _ ⟨hp.ne_zero⟩
    ).insert w).insert (star w)) (.mk' (χ ∘ ideleAt w ∘ star) (by simp)) (isOpen_of_forall_pow_mem
    hp.ne_zero (T := χ.ker) (by simpa)).preimage_of_continuous (by tauto)
  replace ht h x e := (pow_eq_one_iff_of_coprime (.of_dvd_left
    ((w.natCast_mem_iff_dvd h).1 w.1.absNorm_mem) (by simp))).1 ⟨hχ _, map_pow χ .. ▸ ht x e⟩
  have h₆ := by simpa [star_locIdele, hw.symm] using h w
  have h₅ x := by simpa [*, star_locIdele (v := w) x ▸ h ..] using
    QZChar.abelianLift_symmetrise ν (locIdele w x)
  replace h {A u} (hA : IsPlaceOver A u) (a : star u = u ∨ ↑p ∈ u.1) :=
    (hA.artinAt_units_trivial_iff_unramified (QZChar.symmetrise ν)).1 fun x b ↦ by_cases (by aesop)
    fun _ : w ≠ u ↦ by by_cases w = star u <;> subst_eqs <;> cases a <;> simp_all [star_locIdele,
    mt isSplit_of_q_prime, ← artinMap_locIdele, QZChar.abelianLift_symmetrise]
  obtain ⟨⟨_, hg₀, e₀⟩, u, _, ⟨⟩⟩ := (hA.range_abelianLift_artinAt _).le ⟨_, h₅ x₀⟩,
    hA.exists_above (L := QZChar.stepField ν)
  obtain ⟨_, ⟨⟩⟩ := isStep_stepField ν hp hν (e₀ ▸ h₁) (h · ∘ .inr)
  simp [← hA.ncard_above_mul_relIndex (QZChar.ker (QZChar.symmetrise ν)), Nat.prime_mul_iff,
    Set.ext_iff, LE.le] at hp hg₀
  use ν, u, (nonempty_weilData_of_unramified fun v e ↦
    QZChar.not_dvd_differentIdeal_stepField _ (h · ?_)).some <;> grind -zetaDelta -abstractProof [below_star]

open IsDedekindDomain HeightOneSpectrum Nat ZMod decompGroup QuadField algebraMap

attribute [local simp] QZChar.comap mul_mem_right mul_mem_left two_smul neg_eq_self NeZero.ne

/-- For E stably unramified, n ≠ 0, some χ gives a step E' ⊃ ℚ(√−D), split above n. With N =
G_{E'} ∩ ker χ: G_E = NH if H contains inertia at all x ∤ n of small norm; at w ∣ n, G_w
fixes E', and χ kills I_w, and G_w if w is split. -/
lemma exists_quadratic_step E [Field E] [EmbeddedNumberField E] [IsCMField E] [StablyUnram E]
  (n : ℕ) (hn : n ≠ 0) : ∃ χ : QZChar Gal(Ω/E), let E' := stepField χ; let U := ker (symmetrise χ)
    let N := U ⊓ ker χ; ∃ᵉ (D) (_ : HasQuadSubfield D E'), IsStep E' (ideleChar χ) ∧ (∃ m, ∀ H :
      Subgroup Gal(Ω/E), inertiaAbove {x : FinPlace E | ↑n ∉ x.1 ∧ x.q ≤ m} ⊆ H → ∀ g, ∃ h ∈ H,
      g * h ∈ N) ∧ (∀ u : FinPlace E', ↑n ∈ u.1 → IsSplitPrimeToDisc (u.below (QuadField D))) ∧
      ∀ {A : ClosurePlace} {w : FinPlace E}, IsPlaceOver A w → ↑n ∈ w.1 →
    decompGroup _ A ≤ U ∧ inertiaGroup _ A ≤ N ∧ (w.IsSplit → decompGroup _ A ≤ N) := by
  let k := Ideal.absNorm (span {(4 : 𝓞 E)})
  let R := 4 * n * (2 * n) ^ k
  have ⟨j, b, O⟩ := @exists_eq_two_pow_mul_odd R (by aesop)
  let C := 1 + b * (2 + 8 * b)
  have ⟨q, g, p, f⟩ := @forall_exists_prime_gt_and_eq_mod R ⟨by aesop⟩ _ (-unitOfCoprime C (by
    cases j <;> simp [*, C, coprime_mul_iff_right, parity_simps]))⁻¹.isUnit
    (C * n * Ideal.absNorm (differentIdeal ℤ (𝓞 E)))
  let D := C * q
  obtain ⟨⟨M, hD⟩, Z, _⟩ := (natCast_eq_zero_iff (D + 1) R).1 (by simp [D, f,
    neg_add_eq_zero]), (eq_zero_of_dvd_of_lt · g), Fact.mk p
  obtain ⟨d, ⟨P, r⟩, ⟨i, ω, _⟩, ⟨⟩, s, t, l⟩ := Fact.mk (by lia : D % 4 = 3),
    FinPlace.exists_natCast_mem E q, ‹StablyUnram E›.exists_i_c₀, exists_wellFoundedLT (FinPlace E),
    @Prime.sq_add_sq q _ (by grind [C.mul_mod q 4])
  simp [p.dvd_mul, ← P.natCast_mem_iff_dvd r, *] at Z
  have ⟨α, _⟩ : ∃ α : 𝓞 E, α * star α = D :=
    ⟨(1 + 2 * b * ω) * (s + t * i), by simp [D, ← l]; grind⟩
  obtain ⟨B, s, hs⟩ := P.isPlaceOver_placeOver,
    @exists_forall_sub_mem_ideal _ _ _ (@finite_natCast_mem _ _ _ _ ⟨hn⟩)
    (·.1.1 ^ k) (fun _ _ ↦ by grind [isCoprime_pow_of_ne]) fun w ↦ ite (star w.1 < w) α 1
  have N {w : FinPlace E} (h : 2 * n.cast ∈ w.1) :
    ↑(D + 1) ∈ w.1 ^ k := by simp [hD, R, pow_mem_pow h]
  let t := ite (s = 0) 1 (s * star s)
  have T {w} (h : ↑n ∈ asIdeal w) : 1 - α * t * ite (w < star w) i (star α) ^ 2 ∈ w.1 ^ k ∨ star w =
    w ∧ α * t ∉ w.1 ∧ 2 ∉ w.1 := by grind [hs ⟨w, h⟩, =_ Quotient.eq_zero_iff_mem, star_star,
    one_notMem w.1, IsConcreteLE.le_iff, Ideal.mem_comap, le_comap_pow _ k (hs ⟨star w, by simpa⟩),
    pow_le_self, show k ≠ 0 by simp [k], starRingEnd_apply, mem_star_place, → w.2.2]
  obtain ⟨⟨b, hb⟩, ⟨G, -, U⟩, _⟩ := IsAIC.exists_pow_eq 2 (↑(↑(α * t) : E) : Ω), B.decompGroup_spec
    Gal(Ω/E), by simpa [addOrderOf_eq_prime_iff] using QZ.addOrderOf_mk_inv two_pos
  have S (g : Gal(Ω/E)) {c : Ω} {x : E} (h : c ^ 2 = x) :=
    eq_or_eq_neg_of_sq_eq_sq (g c) c (by simp [← map_pow, h])
  have L {A w g c} (a : IsPlaceOver A w) hg {x u : 𝓞 E} h (H : 1 - x * u ^ 2 ∈ w.1 ^ k) :=
      (@S g c x h).resolve_right fun e ↦ have o (z : Ω) := A.valuation.map_add_le le_rfl (val_smul
      (σ := g) hg (1 + z * (u : E))).le; mt (Int.natAbs_le_of_dvd_ne_zero ∘
      absNorm_dvd_norm_of_mem) (by simp [k, Nat.lt_pow_self]) (show 4 ∈ w.1 ^ k by
    rw [← intValuation_le_pow_iff_mem, ← valuation_of_algebraMap (K := E)] at *
    grw [← H, ← a.isEquiv.le_iff_le]
    convert mul_le_mul' (o c) (o (-c)) <;> simp [← map_mul, map_ofNat] <;> grind)
  let y := (i / t : E) * b * cmConj b
  have hy : y ^ 2 = ((-D : 𝓞 E) : E) := by
    simp [y, mul_pow, ↓← map_pow, hb, -map_neg, t]; field_simp [ite_eq_iff]
    exact_mod_cast by grind [star_mul, star_star]
  have := by simpa [y] using congr($hy = 0)
  let χ : QZChar _ := ⟨_, ((isLocallyConstant_smul b).comp (if · = b then 0 else .mk
    2⁻¹)).continuous, fun g h ↦ by cases S g hb <;> cases S h hb <;> simp [*]⟩
  have H {g} : (symmetrise χ).1 g = 0 ↔ g y = y := by cases S g hb <;> cases S g (by
           rw [← map_pow cmConj, hb, cmConj_algebraMap]) <;> simp [*, y, χ, conjGal]
  have Y {A w} a h g m := H.2 (@L A w g _ a m _ 1 hy (by simpa [add_comm] using N h))
  have ⟨σ, I, J⟩ := G.exists_inertia_smul_eq_of_pow_eq (@U (.mk0 _ (by simp)) (B.isUniformiser_iff.2
    (by erw [valuation_of_algebraMap]; simp [D, *, p.ne_zero, -NeZero.ne,
    intValuation_eq_exp_neg_multiplicity, mt dvd_differentIdeal_of_mem_sq (Z.2 <| le_of_dvd
    · (absNorm_mem _)), multiplicity_eq_of_dvd_of_not_dvd (k := 1)]))) two_pos hy (neg_sq y)
  have J := mt H.1 (J.trans_ne (by simpa [y]))
  let := (@embOfSqrt D (stepField χ) _ _ ⟨y, (H.1 ·.2)⟩ _ (by ext; simp [*])).toAlgebra
  use χ, D, {}, (isStep_stepField χ prime_two (by ext; simp [χ, ite_add_ite, *]) J fun a h ↦ (Y a
    (by simp_all) · ·.1)).1, ⟨P.q, fun U e g ↦ .imp' _ (fun i : Fin 2 × Fin 2 ↦ (⟨mul_mem (pow_mem
    (e ⟨P, ?_, _, B, I⟩) i.1) (pow_mem (e ⟨_, ?_, _, B.conjPlace_star, I.conjPlace_conjGal⟩) i.2),
    ·⟩)) (Not.imp_symm (by simp [↓map_mul, toHom, χ, ← ofAdd_add]; split_ifs <;> simp [*]) J)⟩,
    fun u h ↦ ((u.below _).2.2 ((c₀_mul_one_sub D).substr ?_)).elim
    (fun _ ↦ ⟨0, ?_, 1, 1, by simp⟩)
    (⟨1, by simpa using neg_mem ·, -1, -1, ?_⟩), fun a l ↦
      (fun y ↦ ⟨y, fun g i ↦ ⟨y _ i.1, ite_eq_left
    ((T l).elim (L a i.1 hb) fun _ ↦ inertia_fixes_root_of_unit i (a.valuation_natCast_eq_one_iff.2
    ?_) hb (a.valuationVia_eq_one_iff.2 ?_) ?_)⟩, fun e _ g ↦ ⟨y _ g, ite_eq_left (L a g hb ((T
    l).resolve_right ?_))⟩⟩) (Y a ?_) <;> simp [↓valuation_eq_one_iff_notMem, *, -O, R, mul_assoc]

end

/-- Let f' be a weak base change of the eigenform f to E', cut out by χχᶜ, with attached r'.
Some continuous semisimple ρ on N = G_{E'} ∩ ker χ approximates the Hecke polynomials of f;
any r attached to f inherits finite type, jumps, and on N determinants and killing
polynomials. -/
lemma IsWeakBaseChange.exists_attached_descent {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E n M M'} [Field E]
  [CMType E] [EmbeddedNumberField E] [Fintype n] {χ : QZChar Gal(Ω/E)} {f : _ → M → ℂ} {f' :
  Gf (QZChar.stepField χ) n → M' → ℂ} {S P P'} {r' : GalRep ℓ _ n} (hs : IsWeakBaseChange
  (QZChar.ideleChar χ) S f f') (hr' : Attached P' r') (he' : IsEigenform f' P') (he : IsEigenform f
  P) : let L := QZChar.stepField χ; let N := QZChar.ker (QZChar.symmetrise χ) ⊓ QZChar.ker χ
    let i : N →* _ := L.fixingSubgroupEquiv.toMonoidHom.comp (Subgroup.inclusion (id fun s h ↦
      (·.2 ⟨s, h.1⟩))); N.IsOpen ∧ (∀ {r : GalRep ℓ E n}, Attached P r → ∀ A, (IsFiniteTypeAt r' A →
    IsFiniteTypeAt r A) ∧ (∀ {κ} m, HasJumpsAt r' A (jumps κ.baseChange m) → HasJumpsAt r A
      (jumps κ m)) ∧ ∀ s, (r s.1).1.det = (r' (i s)).1.det ∧ ∀ Q, PolyKillsAt r' A (i s) Q →
      PolyKillsAt r A s Q) ∧ ∃ ρ : N →* _, Attached P ρ (·.1) ∧ ∀ s, ρ s = r' (i s) := by
  intro L N i
  obtain ⟨hφ, o⟩ := isOpenEmbedding_galois_restrict (Γ' := Gal(Ω/L))
    (AlgEquiv.restrictScalarsHom E) (by simp), (QZChar.isOpen_ker _).inter (QZChar.isOpen_ker χ)
  refine (fun c ↦ ⟨o, fun h A ↦ ?_, r'.comp i, c, by simp⟩) ⟨hr'.1.comp (hφ.continuous_iff.2
    continuous_subtype_val), (hr'.2.1.comp L.fixingSubgroupEquiv.toMonoidHom).comp _,
    o.isOpenMap_subtype_val, (hr'.2.2.2 · · |>.and (eventually_mostFrobenii he'.2 fun y ↦
    (· y.prime_q)) |> mostFrobenii_push hφ _ |>.mp (eventually_mostFrobenii
    (he.2.and ((finite_ramified o).and hs.1.cj.compl_mem_cofinite)) fun x ⟨y,
    I, z⟩ B s e ↦ x.isPlaceOver.exists_above.rec fun u ⟨a,
    i⟩ ↦ have D : _ ≤ N := x.isPlaceOver.decompGroup_le x.isFrob o (I _ x.isPlaceOver) (by bound)
    have G := x.isPlaceOver.split_completely fun _ h ↦ (D h).1
    (B ⟨_, _, _, (G u i).1 ▸ x.prime_q, a, (G u i).1 ▸ (e ▸ x.isFrob :)⟩ i (by tauto)).rec fun b d ↦
      (show _ → _ → P' u = P x.w by simp_all [HasHeckePolyAt, heckePoly, he'.1, smul_left_inj]) d.2
      ((hs.2 _ z u i).2 ⟨by simp [(x.isPlaceOver.artinAt_trivial_iff_decompGroup_le _).2 fun _ h ↦
      (D h).2], G⟩ _ _ (y x.prime_q).2).2 ▸ b _ rfl))⟩
  choose Z h using c.2.1.exists_conj_of_trace_eq _ (.id ..) (h.2.1.comp N.subtype).hasSemiprimeSpan
    (c.trace_eq h · rfl)
  refine (local_clauses_of_retract 1 (algebraMap ..) (by simp) (by simp) hφ ((hφ.continuous.1 _
    o).mem_nhds N.one_mem) (fun _ ↦ (h ⟨_, ·⟩)) Z.4).imp_right (.imp (fun b _ _ ↦
    b Z.3 ∘ cast ?_) fun c s ↦ ⟨by simpa [field] using! congr($(h s).det).symm, @c _ s.2⟩)
  simp [jumps.eq_unfold]; congr!; apply CMOver.mem_type_iff

open Finset Matrix Fintype Filter Representation

attribute [local simp] smul_smul map_smul' _root_.zpow_mul scalarFin coe_divStar

/-- For r attached to a rank n eigenform f, det r is the avatar of an algebraic Hecke character
θ of explicit type; at split w, θ_w gives eigenvalues of unit scalars on f, and (−1)^n Q(0)
at uniformisers, Q a Hecke polynomial of f. -/
lemma Attached.exists_det_eq_avatar {E n} [Field E] [Fintype n] [CMType E] {κ ℓ}
    [ThePrime ℓ] [PadicIso ℓ] [Algebra E Ω] {f P} {r : GalRep ℓ E n} (hr : Attached P r) (hf : f ∈
  (stdSpace E n).forms κ) (he : IsEigenform f P) : ∃ θ : AlgHeckeChar E, (∀ σ, θ.1.2.toAdd σ =
  (if σ = Φ (.mk σ) then 1 else -1) * (card n * κ.2 (.mk σ) + ∑ i ∈ .range (card n),
  i * κ.1 (.mk σ) i) - (card n).choose 2) ∧ (∀ w (hw : star w ≠ w) x, (Valued.v x.1 = 1 → ∀ {c : ℂ},
  rightRegular ℂ _ _ (atSplit hw (.scalar n x)) f = c • f → θ.1.1 (locIdele w x) = c) ∧
  (Valued.v x.1 = .exp (-1) → ∀ {Q}, HasHeckePolyAt f w hw Q → θ.1.1 (locIdele w x) =
  (-1) ^ card n * Q.coeff 0)) ∧ ∀ g, (r g).1.det = AlgHeckeChar.avatar θ g := by
  let z := (scalarFin (E := E) n).comp divStar.1
  choose χ _ e using
    exists_monoidHom_extend (.domRestrict (.fst _ ℂˣ) (Subgroup.mk ⟨⟨{p | rightRegular ℂ _ _ (z p.1)
    f = p.2 • f}, by simp_all [mul_comm]⟩, by simp⟩ (by simp_all))) (.domRestrict
    (.snd ..) _) ⊥ fun a e ↦ Units.ext ((smul_left_inj he.1).1 (a.2.symm.trans (by simp_all)))
  have h x c (h : rightRegular ℂ _ _ (z x) f = c • f) : (χ x).1 =
    c := congr($(e ⟨(x, .mk0 c fun _ ↦ by
      simp_all [IsEigenform, ← inv_apply_eq_iff, eq_comm]), h⟩).1)
  refine ⟨IsHeckeOfType.toAlgebraic (k := -2 * (card n).choose 2) (by simp; lia)
    ⟨((rightStab f).comap z).isOpen_mono (e ⟨⟨·, 1⟩, by simpa using! funext ·⟩) (hf.1.preimage
    ((U.isClosedEmbedding_mat (by simp)).continuous_iff.2 (.matrix_diagonal (by simp; fun_prop)))),
    fun x ↦ ?_⟩, congrFun (toAdd_ofAdd _), (and_iff_left_of_imp fun H g ↦ ?_).2 fun w hw x ↦ ?_⟩
  · simp [← prod_mul_distrib, -neg_add_rev, ← two_mul, ← mul_zpow, div_pow, sq (Φ _ _),
      ← Complex.conj_mul', mul_div_mul_right, h (principalIdele x) _ (by simp [funext_iff, fun g ↦
              (Subtype.ext (by ext; simp [z, mul_comm, division_def]) : g * z (principalIdele x)
      = stdEmbFin (U.of (by simp) ((x.1 / star x.1) • 1) (by simp)) * g), stdSpace_weightRep_apply,
              hf.2 _, weylRep, Units.smul_def, schur_smul, @starRingEnd_apply E,
              ← prod_mul_distrib, ← zpow_add₀, ← zpow_natCast, ← _root_.zpow_mul]; tauto)]
  · exact (det_eq_sign_charpoly_coeff _).trans (tendsto_nhds_unique
      ((hr.tendsto_charpoly_coeff ..).const_mul _)
     ((tendsto_mostFrobeniiAt (AlgHeckeChar.avatar _ · |>.1)).congr' (mem_inf_of_left
      ((AlgHeckeChar.eventually_avatar_frob _).mp (eventually_mostFrobenii he.2 fun y a e ↦ e.trans
      (by simpa [heckeCoeff] using congr(ιℓ $((H ..).2 (v_uniformizer _) (a y.prime_q).2))))))))
  have h := (Subtype.ext (Units.ext (by simp [z]; simp [atSplit, ← map_inv, locGL, locIdele, ←
    diagonal_one, star_eq_conjTranspose])) : z (locIdele w x) = atSplit hw (.scalar n x)) ▸ h _
  exact ⟨(by simp [·, h · ·]), fun hx _ ⟨m, _, _, ht⟩ ↦ by simp [*, h _ (by erw [← ht,
    ← heckeSplit_dual hw 0 _ m hx (zero_add _).symm, heckeGL_zero (by rwa [← mem_sphericalAt_iff,
    sphericalAt, maxCompactAt, Gf.supportedOn_star])]), ← Complex.ofReal_pow, field, ← pow_mul']⟩
