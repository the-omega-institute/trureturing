/- GID: D5/S3/Zeros/GRH/New/Data/WeilDataOfE
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Data/WeilDataOfE
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Data.WeilDataOfE. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Data/WeilDataOfE.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Data.Different
import D5.S3.Zeros.GRH.Lib.ClassField.HeckeCharacter.SplittingCharExists
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

This file: Decomposition of primes and Frobenius in a cyclotomic extension of an imaginary quadratic
field. Weil data for E: cyclotomic unit, idele of half the different, splitting character. -/

open Algebra Ideal CharP FiniteField QuadField NeZero NumberField Polynomial ZMod
  IsDedekindDomain.HeightOneSpectrum NumberField.RingOfIntegers

namespace Parameters

attribute [local simp] coe_frobeniusAlgHom ne placeOfInt_pow map_ofNat neg_one_pow_eq_ite

variable {P : Parameters} {s} {p : ℕ} [hp : Fact p.Prime] {R} [CommRing R] [CharP R p] {v :
  P.Φ s} {w w' : FinPlace (P.E s)} (h : ¬p ∣ P.N₁ s) (φ : 𝓞 (P.E s) →+* R) (n) {c e} (he : c =
  RingEquiv.refl (𝓞 (P.E s))
  ∧ e = 1 ∨ c = starRingAut ∧ e = -1) (g : p ≡ 1 [MOD P.N₁ s * P.d]) (hw : ↑p ∈ w.1) (hc : ¬p ∣ P.N₁
  s * P.d) (hL : chiK P.d p = -1) {a : 𝓞 (P.E s)} (ha : ∃ c : ℕ, a * star a = p * c ∧ p.Coprime c)

/-- The ring endomorphism of 𝓞_E given by the element σ_v of Gal(E/K) attached to the infinite
place v. -/
noncomputable def galOfPlaceInt v := MulSemiringAction.toRingHom _ (𝓞 (P.E s)) (P.galOfPlace s v)

@[simp] lemma coe_galOfPlaceInt x : galOfPlaceInt v x = P.galOfPlace s v x := rfl

noncomputable instance : SMul (P.Φ s) (FinPlace (P.E s)) := ⟨(.comap <| P.galOfPlace s ·)⟩

/-- An integer x of E lies in the prime v • w if and only if σ_v x lies in w, where σ_v ∈
Gal(E/K) is attached to the infinite place v. -/
@[simp] lemma mem_smul {x} : x ∈ (v • w).1 ↔ galOfPlaceInt v x ∈ w.1 := .rfl

/-- The pair (place named by (p/d)·p, Legendre symbol (p/d)) in Φ × ℤ; for primes p ∤ N₁d it is
the Frobenius element at p in Gal(E/ℚ) = Φ × {±1}. -/
@[simp] noncomputable def frobElem (p : ℕ) := (P.placeOfInt n (chiK P.d p * p), chiK P.d p)

include h in
lemma isCoprime_N₀_of_not_dvd :
  IsCoprime (p : ℤ) P.N₀ := mod_cast by grind [hp.1.coprime_iff_not_dvd]

include h he in
/-- Let p ∤ N₁ be prime, φ : 𝓞_E → R, char R = p, (c, e) = (identity, 1) or (conjugation, −1). Then
φ(σ_v x) = φ(cx)^{pⁿ} for all x iff φ(σ_v ζ) = φ(σ_u ζ), u the place named by epⁿ, and (p/d)ⁿ e
φ(√−d) = φ(√−d). -/
lemma frob_ext : (∀ x, φ (galOfPlaceInt v x) = φ (c x) ^ p ^ n) ↔ φ (galOfPlaceInt v
  (P.zetaInt s)) = φ (galOfPlaceInt (P.placeOfInt s (e * p ^ n)) (P.zetaInt s)) ∧ chiK P.d p ^ n *
  e * φ (P.sqrtNegDInE s) = φ (P.sqrtNegDInE s) := .trans ⟨fun e ↦ And.intro (e (zetaInt ..))
  (e (c₀InE ..)), fun _ x ↦ by induction (adjoin_eq_adjoin_union ℤ _ _
  (different_eq_span_and_adjoin_c₀ _).2).le ((relDifferent_spec isPrimitiveRoot_zetaInt).2.2.ge
  (x := x) ⟨⟩) using adjoin_induction <;> simp_all [← iterateFrobenius_def]; lia⟩ (by
  erw [← map_pow,
    eq_map_c₀_pow_iff (h <| · ▸ by grind [Parameters] : p ≠ 2) (φ.comp (c.toRingHom.comp _))]
  congrm _ = φ ?_ ∧ ?_ <;> cases he <;> simp [*, RingOfIntegers.ext_iff,
    (isCoprime_N₀_of_not_dvd h).pow_left, galOfPlace_placeOfInt_zeta, IsCoprime.neg_left,
    star_c₀InE, galOfPlaceInt.eq_1 v, sqrtNegDInE] <;> norm_cast <;> grind)

include he hc in
lemma frob_iff_eq_frobElem_pow [IsDomain R] : (∀ x, φ (galOfPlaceInt v x) = φ (c x) ^ p ^ n) ↔
  (v, e) = P.frobElem s p ^ n := by
  rw [hp.1.dvd_mul, not_or] at hc
  rcases of_not_dvd R hc.1, chiK_cases P.d p, (hc.1 <| · ▸ by grind [Parameters] : p ≠ 2),
    em (Even n)
  simp [val_lt, (val_injective _).eq_iff, Units.val_inj, (isRoot_cyclotomic_iff.1 (map_cyclotomic _
    φ ▸ (isPrimitiveRoot_zetaInt.isRoot_cyclotomic one_le).map)).injOn_pow.eq_iff,
    frob_ext hc.1 φ n he, (Subtype.ext (galOfPlace_zeta _) : galOfPlaceInt _ (zetaInt ..) =
    zetaInt .. ^ _), mul_left_eq_self₀, placeClass, mul_pow]
  erw [← sq_eq_zero_iff, map_sqrtNegDInt_sq (.comp ..)]
  casesm* _ ∨ _, _ ∧ _ <;> simp_all [_root_.neg_one_eq_one_iff, ringChar.eq, ringChar.spec]

attribute [local instance] Quotient.field ZMod.algebra

include he hw hc in
/-- Decomposition group: let w lie above a prime p ∤ N₁d, and (w', e) = (w, 1) or (w̄, −1). Then
v ∈ Φ, acting by preimage of prime ideals, sends w to w' iff (v, e) is a power of the
Frobenius element `Parameters.frobElem`. -/
lemma smul_eq_iff_exists_frobElem_pow : v • w = comap c c.surjective w ↔ ∃ n, (v, e) =
  P.frobElem s p ^ n := have := w.charP_quotient hw
  ⟨fun H ↦ by
    exact ((bijective_frobeniusAlgHom_pow (ZMod p) _).2 (.mk' (quotientMap _ ((galOfPlaceInt v).comp
      c.symm) ((reindex_equiv c).1.2 (by simpa using! congr($H.1).ge))) (ZMod.map_smul _))).rec fun
      n e ↦ ⟨n, (frob_iff_eq_frobElem_pow _ n he hc).1 fun x ↦ by simpa using congr($e.symm (c x))⟩,
    fun ⟨n, H⟩ ↦ by ext; show _ ↔ c _ ∈ w.1; simp [← @Quotient.eq_zero_iff_mem _ _ w.1,
    (frob_iff_eq_frobElem_pow _ n he hc).2 H]⟩

/-- For a place w of E above a prime p ∤ N₁d, the norm of w is p^o, with o the order of the
Frobenius element `Parameters.frobElem` at p. -/
lemma q_eq_pow (hw : ↑p ∈ w.1) (hc : ¬p ∣ P.N₁ s * P.d) : w.q = p ^ orderOf (P.frobElem s p) := by
  obtain ⟨_, ⟨⟩⟩ := w.charP_quotient hw, w.exists_q_eq_pow hw
  simp [*, galOfPlaceInt, p.pow_right_inj Fact.out, ← Nat.dvd_right_iff_eq, eq_comm,
    -frobElem, orderOf_dvd_iff_pow_eq_one, ← frob_iff_eq_frobElem_pow (Ideal.Quotient.mk w.1)]

include hw hc in
lemma natCast_notMem_sq : ↑p ∉ w.1 ^ 2 := hc ∘ (w.natCast_mem_iff_dvd hw).1 ∘
  (le_of_dvd · cycloConductor_mem_different) ∘ dvd_differentIdeal_of_mem_sq

include hw hc in
/-- If p is a prime not dividing N₁d and w is a finite place of E above p, then p has order
exactly 1 at w (multiplicative valuation exp(−1)); so p is unramified at w. -/
lemma intValuation_p : w.intValuation p = .exp (-1) := by simp [*, natCast_notMem_sq,
  intValuation_eq_exp_neg_multiplicity, multiplicity_eq_of_dvd_of_not_dvd (k := 1)]

/-- If the finite places w and w' of E lie above the same prime p, then some element of Φ =
Gal(E/K), named by an infinite place v, sends w to w' or to its complex conjugate. -/
lemma exists_smul_eq_or_star (hw : ↑p ∈ w.1) (h : ↑p ∈ w'.1) : ∃ v : P.Φ s, v • w = w' ∨
  star (v • w) = w' := (IsInvariant.exists_smul_of_under_eq ℤ _ Gal(P.E s/ℚ) w'.1 w
  (by ext (_ | _) <;> simp [*, -Nat.cast_add, @FinPlace.natCast_mem_iff_dvd _ _ _ p])).rec fun g _ ↦
  ⟨_, by refine (Φ_eq_or ((Φ 1).comp g.toRingHom)).imp ?_ ?_ <;> intro e <;> ext <;> simp <;>
  convert smul_mem_pointwise_smul_iff <;> ext <;> apply (Φ 1).injective <;>
  simpa [← phi_mul] using! congr($e _)⟩

@[local simp] lemma not_dvd_N₁_mul_d_of_inert (hL : chiK P.d p = -1) : ¬p ∣ P.N₁ s * P.d := by
  grind [chiK_eq_one_of_dvd, Fact, chiK_cases, hp.1.dvd_mul, p.prime_dvd_prime_iff_eq]

include hw hL

/-- Let p be a prime with (p/d) = −1 and w a place of E above p. An element v of Φ = Gal(E/K)
fixes w if and only if v is an even power of the class of −p. -/
lemma smul_eq_iff_inert : v • w = w ↔ ∃ n, v = P.placeOfInt s (-p) ^ n ∧ Even n := by
  simpa [*] using! smul_eq_iff_exists_frobElem_pow (.inl ⟨rfl, rfl⟩) hw

/-- Let p be a prime with (p/d) = −1 and w a place of E above p. An element v of Φ = Gal(E/K)
sends w to w̄ if and only if v is an odd power of the class of −p. -/
lemma smul_eq_star_iff_inert : v • w = star w ↔ ∃ n, v = P.placeOfInt s (-p) ^ n ∧ Odd n := by
  simpa [*] using! smul_eq_iff_exists_frobElem_pow (.inr ⟨rfl, rfl⟩) hw

/-- Let p be a prime with (p/d) = −1 and w a place of E above p. Then Nw = p^{lcm(o, 2)}, where
o is the order of the class of −p in Φ = (ℤ/N₁)^×. -/
lemma q_eq_inert : w.q =
  p ^ (orderOf (P.placeOfInt s (-p))).lcm 2 := by simp [q_eq_pow hw, *, Prod.orderOf]

omit hw hL

include g

omit [Fact p.Prime] in
lemma chiK_eq_one_of_modEq_one : chiK P.d p = 1 := by simp [natCast_eq_natCast' _ _ g.of_mul_left]

@[local simp] lemma not_dvd_N₁_mul_d_of_modEq_one : ¬p ∣ P.N₁ s * P.d :=
  g.dvd_iff.mt (by simp [hp.1.ne_one])

omit [Fact p.Prime] in
/-- For p ≡ 1 mod N₁d, the Frobenius element `Parameters.frobElem` at p is trivial. -/
lemma frobElem_eq_one : P.frobElem s p = 1 := by simp [placeOfInt, chiK_eq_one_of_modEq_one g,
  natCast_eq_natCast' _ _ g.of_mul_right]

include hw

/-- If w is a place of E above a prime p ≡ 1 mod N₁d, then no element of Φ = Gal(E/K) sends w to
its complex conjugate w̄. -/
lemma smul_ne_star : v • w ≠ star
  w := by simpa [↓frobElem_eq_one, *] using! smul_eq_iff_exists_frobElem_pow (.inr ⟨rfl, rfl⟩) hw

lemma smul_eq_self_iff_eq_one : v • w = w ↔ v = 1 := by
  simpa [↓frobElem_eq_one, *] using! smul_eq_iff_exists_frobElem_pow (.inl ⟨rfl, rfl⟩) hw

/-- If p is a prime ≡ 1 mod N₁d, every finite place w of E above p has absolute norm p. -/
lemma q_eq_of_modEq_one : w.q = p := by simp [q_eq_pow hw, ↓frobElem_eq_one, *]

include ha

/-- Let w be a place of E above a prime p ≡ 1 mod N₁d, and a ∈ 𝓞_E with aā = pc, c a natural
number prime to p. Then w divides exactly one of a and ā. -/
lemma star_mem_iff : star a ∈ w.1 ↔ a ∉ w.1 :=
  ha.rec fun _ c ↦ by grind [mul_mem_right, natCast_notMem_sq
  hw (by aesop), sq, mul_mem_mul, w.2.mem_pow_mul, w.2.notMem_of_isCoprime_of_mem c.2.cast hw]

/-- Let p ≡ 1 mod N₁d be prime, w a place of E above p, and a ∈ O_E with aā = pc for a natural
number c prime to p. If a lies in w, then a has valuation exactly 1 at w. -/
lemma intValuation_eq_of_mul_star (k : a ∈ w.1) : w.intValuation a = .exp (-1) := by
  grind [intValuation_p, not_dvd_N₁_mul_d_of_modEq_one, intValuation_eq_one_iff, star_mem_iff,
    w.natCast_mem_iff_dvd, hp.1.coprime_iff_not_dvd, map_mul w.intValuation a (star a)]

omit hw

/-- Let p ≡ 1 mod N₁d be prime and a ∈ O_E with aā = pc, c a natural number prime to p. Then the
infinite places of E are in bijection with the finite places containing both a and p. -/
lemma nonempty_infinitePlace_equiv_finPlace : Nonempty (P.Φ s ≃ {w : FinPlace _ // a ∈ w.1 ∧
  ↑p ∈ w.1}) := by refine (FinPlace.exists_natCast_mem _ p).rec fun w _ ↦
  ⟨.ofBijective (fun v ↦ ⟨ite (a ∈ (v • w).1) (v • w) (star (v • w)), ?_⟩)
  ⟨fun u v ↦ have : v • w = (u⁻¹ * v) • u • w := by ext; simp [galOfPlaceInt, smul_smul]
  ?_, fun _ ↦ ?_⟩⟩ <;> grind [mem_star_place, star_mem_iff, mem_smul, map_natCast, star_natCast,
  exists_smul_eq_or_star, star_star, smul_ne_star, smul_eq_self_iff_eq_one, inv_mul_eq_one]

end Parameters

variable {P : Parameters} {s}

/-- For every injective ring endomorphism φ of 𝓞_E and every finite place w of E, the elements
φ(P'(ζ)) and P'(ζ) have the same w-adic valuation, where P'(ζ) = `Parameters.relDifferentGen`
generates the different of E/K. -/
lemma Parameters.valuation_map_relDifferentGen (f : _ →+* 𝓞 (P.E s)) (h : (⇑f).Injective) (w :
  FinPlace (P.E s)) : w.valuation _ (f (P.relDifferentGen s)).val =
  w.valuation _ (P.relDifferentGen s).val := by simp [↓valuation_of_algebraMap, intValuation_def,
  ← span_singleton_eq_bot, ← eval_map_apply, ← derivative_map, relDifferent_spec,
  isPrimitiveRoot_zetaInt.map_of_injective h, isPrimitiveRoot_zetaInt]

/-- The finite idele α with component 1/P'(ζ) at the places dividing c₀ = (1 + √−d)/2 and 1
elsewhere, P'(ζ) = `Parameters.relDifferentGen`. -/
noncomputable def Parameters.α P s := let e := idem {w | c₀InE P s ∈ w.1}
  (Units.mk0 _ (P.relDifferentGen_ne_zero s))⁻¹.map
    ⟨⟨(e * algebraMap _ _ · + (1 - e)), by simp⟩, by grind [idem_mul_self]⟩

attribute [local simp] valuation_le_one Parameters.star_c₀InE Parameters.α idem_apply mem_Ô
  mul_le_one'

lemma Parameters.inv_α_mem : (P.α s)⁻¹.1 ∈ Ô _ := by aesop

/-- At every finite place w of E, the w-component of α·ᾱ·P'(ζ) is a unit, where α = `Parameters.α`
and P'(ζ) = `Parameters.relDifferentGen` generates the different of E/K. -/
lemma Parameters.v_alpha_mul_relDifferentGen w :
  Valued.v ((P.α s * star (P.α s).1 * P.relDifferentGen s) w) = 1 := by
  simp [-star_add]
  split_ifs <;> simp_all [w.1.sub_mem_iff_left, valuation_map_relDifferentGen _ star_injective _ ▸
    valuation_star w _, one_notMem, mt (w.2.2 ∘ (c₀InE_mul_one_sub ..).substr ∘ w.2.mem_of_pow_mem
    (P.N₁ s) ∘ mem_of_dvd _ (.trans relDifferentGen_dvd_N₁
    (mod_cast .natCast (by grind [(N₁ ..).dvd_pow_self_iff out, dvd_norm_c₀, lt_d]))))]

lemma Parameters.N₁_mul_α_mem : P.N₁ s * (P.α s).1 ∈ Ô _ := by simp_all [field, apply_ite,
  ite_apply, by simpa using congr(($((@relDifferentGen_dvd_N₁ P s).choose_spec).val : 𝔸f (P.E s)))]

/-- `-1/√(-d)`, `P.α s` and a splitting character `υ` are Weil data for `E`. For `υ`: every root of
unity is `δ/δ̄` for a unit `δ` of norm `1` over `K`; `i (ζ - 1)` is such a unit, and its conjugate
is `ζ⁻¹` times it; take powers. -/
noncomputable instance Parameters.instWeilDataE : WeilData (P.E s) := by
  have := (nonempty_splittingChar fun (y : P.E s) h ↦
    (exists_zeta_pow_eq h).choose_spec.2 ▸ let m := P.N₁ s / 4
    have N : Algebra.norm P.K (P.zetaInt s ^ m * (P.zetaInt s - 1)).val = 1 := by erw [map_mul,
                isPrimitiveRoot_zeta.sub_one_norm_eq_eval_cyclotomic, map_pow,
      isPrimitiveRoot_zeta.norm_eq_one, one_pow,
      eval_one_cyclotomic_not_prime_pow fun _ _ _ ↦ ?_] <;> grind [Parameters, ne (P.N₁ s),
      Nat.prime_eq_prime_of_dvd_pow, Nat.prime_two, Nat.prime_three, irreducible_cyclotomic]
    ⟨((RingOfIntegers.isUnit_norm _).1 ⟨1, ext N.symm⟩).unit ^
      (exists_zeta_pow_eq h).choose, by simp [↓prod_phi_eq_norm,
      N, -map_mul], congr($(show P.zetaInt s ^ _ * star _ = _ by simp [← mul_pow]; congr 1; grind
      [star_zetaInt_pow_mul 1, (isPrimitiveRoot_zetaInt.pow one_le (by grind [Parameters] :
      P.N₁ s = m * 2 * 2)).eq_neg_one_of_two_right, star_zetaInt_pow_mul, pow_mul']))⟩).some
  use -(P.sqrtNegDInE s).val⁻¹, ?_, ?_, P.α s, fun w ↦ by simpa [field,
    different_eq_span_relDifferentGen_mul, ← v_algebraMap_eq_intValuation,
    v_algebraMap_eq_valuation] using (congr($(v_alpha_mul_relDifferentGen ..) /
    $(w.intValuation_eq_exp_neg_multiplicity (ne_zero_of_differentIdeal_eq_span
    different_eq_span_relDifferentGen_mul)))), by simp [sqrtNegDInE, map_ofNat, isIntegral_coe],
    exists_eq_principalIdele_mul_norm.2.2 <;> simp [← map_star_CM, pos]
