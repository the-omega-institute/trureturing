/- GID: D5/S3/Zeros/GRH/New/Data/Different
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Data/Different
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Data.Different. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Data/Different.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.Places.CyclotomicCharacter
import D5.S3.Zeros.GRH.New.Endgame.PrimeError
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

Set-up for this proof: dictionaries between two encodings of the same objects.

This file: Parameters N₀, d; fields K, E; infinite places as a group; CM type. Dictionary between
places, Galois elements and residue classes; counts of all infinite places of E and of those
congruent to 1 modulo N₀. Permutation of infinite
places of E by an automorphism of ℂ over K. Roots of unity of K(ζ) are powers of ζ; the norm to K.
Different of K(ζ) over K and ℚ, monogenicity, imaginary generator, its size. -/

noncomputable section

section

open NumberField Polynomial IsCyclotomicExtension jacobiSym InfinitePlace IsAlgClosed cyclotomic
  NeZero IsMulCommutative

/-- The fixed parameters: a positive multiple N₀ of 18480 and a prime d ≡ N₀/2 − 1 mod N₀
(stated as: N₀ divides 2(d + 1), not d + 1). -/
@[local grind] structure Parameters where
  (N₀ d : ℕ)
  dvd_N₀ : 18480 ∣ N₀
  d_prime : d.Prime
  /-- `d ≡ N₀/2 - 1 mod N₀`. -/
  d_congr : N₀ ∣ 2 * (d + 1) ∧ ¬N₀ ∣ d + 1

namespace Parameters

variable (P : Parameters) (s) {p : ℕ}

instance : NeZero P.N₀ := ⟨by grind [zero_dvd_iff]⟩

@[local grind! .] instance instHeegD : PrimeSevenModEight P.d :=
  @.mk _ ⟨P.4⟩ (by grind [→ dvd_trans])

/-- The natural number 3^c 2^s with c = ⌊log₃ s⌋ + 5, so that 81s < 3^c ≤ 243s for s ≥ 1; c = 5
for s = 0. -/
def _root_.towerDeg := 3 ^ (.log 3 s + 5) * 2 ^ s deriving NeZero

/-- The natural number N₁ = 3^c 2^s N₀, where 3^c 2^s = `towerDeg` s. -/
abbrev N₁ := P.N₀ * towerDeg s

/-- Every prime p dividing N₁ divides (d + 1)/4, the norm of (1 + √−d)/2. -/
lemma dvd_norm_c₀ {s} (hp : p.Prime) (h : p ∣ P.N₁ s) : p ∣ (P.d + 1) / 4 := (hp.dvd_or_dvd
  (m := 2 ^ 3) (.trans (by grind [hp.dvd_mul, hp.dvd_of_dvd_pow, dvd_trans, towerDeg]) (P.5.1.trans
  ⟨1, by grind [PrimeSevenModEight]⟩))).elim (by grind [hp.dvd_of_dvd_pow ·, dvd_trans,
  PrimeSevenModEight]) id

lemma lt_d : 64 < P.d := by grind [→ dvd_trans]

/-- Every prime p dividing N₁ = 3^c 2^s N₀ has χ_K(p) = (p/d) = 1, so it splits in K = ℚ(√−d). -/
lemma chiK_eq_one_of_dvd {s} (hp : p.Prime) (h : p ∣ P.N₁ s) : chiK P.d p = 1 := by
  rw [chiK_eq_legendreSym, legendreSym.to_jacobiSym, mod_right', (Nat.mod_eq_sub_iff one_pos _).2,
    ← one_left (4 * p - 1), ← mod_left' (Int.add_emod_right 1 _)] <;>
    grind [hp.pos, Nat.mul_dvd_of_dvd_div, dvd_norm_c₀, =_ div_four_left, PrimeSevenModEight]

lemma thirteen_le_of_chiK_ne_one (hp : p.Prime) : chiK P.d p ≠ 1 → 13 ≤ p := Not.imp_symm fun _ ↦
  P.chiK_eq_one_of_dvd hp (.trans (by interval_cases p <;> trivial) (P.3.mul_right (towerDeg 0)))

/-- The imaginary quadratic field K = ℚ(i√d), as a subfield of ℂ. -/
abbrev K := QuadField P.d

/-- The natural number M_ω = (N₀d)^(s+6); it is the order of the residue characters ω_w at the
chosen places. -/
def Mω := (P.N₀ * P.d) ^ (s + 6) deriving NeZero

/-- The number N₁d divides M_ω = `Parameters.Mω`, for every exponent s. -/
lemma N₁_mul_d_dvd_M_omega {P s} : N₁ P s * P.d ∣ P.Mω s := by grw [mul_right_comm, towerDeg,
  Nat.log_le_self, Mω, s.le_add_right, ← mul_pow, (by grind : 3 * 2 ∣ P.N₀ * _), ← pow_succ']

lemma coprime_N₁_d : (P.N₁ s).Coprime P.d :=
  (P.4.coprime_iff_not_dvd.2 ((P.chiK_eq_one_of_dvd P.4).mt (by simp [chiK]))).symm

/-- The field E = K(ζ) obtained from K by adjoining a primitive root of unity ζ of order N₁ =
3^c 2^s N₀. -/
def E := CyclotomicField (P.N₁ s) P.K deriving Field, Algebra P.K, NumberField

/-- The infinite places of the field E = K(ζ) of exponent s; they carry the group structure of
Gal(E/K) (`Parameters.galOfPlace`). -/
protected abbrev Φ := InfinitePlace (P.E s)

/-- The real number Ω = exp(γ − Re L′/L(1, χ_K))·2π/rd_E, with γ Euler's constant and rd_E the
root discriminant of E. -/
def bigOmega := (chowlaSelbergConst P.d).exp * (2 * .pi / rootDiscr (P.E s))

instance : IsCyclotomicExtension {P.N₁ s} P.K (P.E s) := CyclotomicField.isCyclotomicExtension ..

/-- The N₁-th cyclotomic polynomial is irreducible over K = ℚ(√−d). -/
lemma irreducible_cyclotomic : Irreducible (cyclotomic (P.N₁ s) P.K) := let M := cycloField P.d
  have hζ := zeta_spec (P.N₁ s) M (CyclotomicField (P.N₁ s) M)
  (monic ..).irreducible_of_irreducible_map
    (QuadField.nonempty_algHom_of_isPrimitiveRoot _ (zeta_spec _ ℚ M)).1 _ (by simpa using ((
    associated_of_dvd_of_natDegree_le (minpoly.dvd _ _ (aeval_zeta ..)) (monic ..).ne_zero (by
    simpa [← Module.finrank_mul_finrank ℚ M, (hζ.powerBasis _).finrank, ↓Rat.finrank P.d, pos,
    natDegree_cyclotomic] using
      totient_mul_totient_le_finrank _ _ (coprime_N₁_d ..) hζ ((zeta_spec _ ℚ M).map_of_injective
    (algebraMap ..).injective))).irreducible (minpoly.irreducible (.of_finite ..))))

/-- A chosen ℚ-algebra embedding of E = K(ζ), ζ of order N₁, into the cyclotomic field
ℚ(ζ_{N₁d}). -/
def toCycloField {P s} : E P s →ₐ[ℚ] cycloField (P.N₁ s * P.d) :=
  have hζ := zeta_spec (P.N₁ s * _) ℚ (cycloField (P.N₁ s * P.d))
  let := (QuadField.nonempty_algHom_of_isPrimitiveRoot P.d (hζ.pow one_le rfl)).toAlgebra
  (SplittingField.lift _ (by simp [cyclotomic_eq_prod_X_sub_primitiveRoots (hζ.pow one_le
    (mul_comm ..))])).toRatAlgHom

instance : IsAbelianGalois ℚ (P.E s) := (isAbelianGalois {P.N₁ s * P.d} ..).of_algHom toCycloField

instance : IsAbelianGalois P.K (P.E s) := .tower_top ℚ ..

instance : IsTotallyComplex (P.E s) := isTotallyComplex_of_algebra P.K _

lemma algHom_eq_of_mk_eq {φ ψ : P.E s →ₐ[P.K] ℂ} (h : InfinitePlace.mk φ.1 = .mk ψ.1) : φ = ψ :=
  (mk_eq_iff.1 h).elim (by grind [AlgHom]) (by simpa using congr($(·).comp (algebraMap P.K _)))

/-- `Gal(E/K)` acts simply transitively on the infinite places. -/
instance : CommGroup (P.Φ s) := (Equiv.ofBijective (fun g : Gal(P.E s/P.K) ↦
  InfinitePlace.mk (lift.comp g.toAlgHom).1) ⟨fun _ _ h ↦ AlgEquiv.ext (lift.injective
  congr($(P.algHom_eq_of_mk_eq s h) ·)), fun _ ↦ (exists_smul_eq_of_comap_eq (w := .mk lift.1)
  (by subsingleton)).elim (⟨·⁻¹, ·⟩)⟩).symm.commGroup

/-- The isomorphism v ↦ σ_v from the group of infinite places of E to Gal(E/K): the place named
by a goes to the automorphism ζ ↦ ζ^a. -/
def galOfPlace : P.Φ s ≃* Gal(P.E s/P.K) := Equiv.mulEquiv _

/-- The group isomorphism from the group Φ of infinite places of E to (ℤ/N₁)^×: the
identification Φ = Gal(E/K) (`Parameters.galOfPlace`) followed by the cyclotomic character. -/
def placeMulEquiv := (P.galOfPlace s).trans (autEquivPow _ (P.irreducible_cyclotomic s))

/-- The infinite place of E named by the class of the integer ν modulo N₁ if ν is prime to N₁,
and the identity place otherwise. -/
def placeOfInt ν := if h : IsUnit (Int.cast ν) then (P.placeMulEquiv s).symm h.unit else 1

/-- For a divisor m of N₁, the homomorphism from the group of infinite places of E, identified
with (ℤ/N₁)^×, to (ℤ/m)^× given by reduction modulo m. -/
def placeClass {s m} (d : m ∣ P.N₁ s) := (ZMod.unitsMap d).comp (P.placeMulEquiv s).toMonoidHom

/-- A chosen primitive N₁-th root of unity ζ in E. -/
def ζ := zeta (P.N₁ s) P.K (P.E s)

/-- The embeddings over `K`. -/
instance : CMType (P.E s) :=
  {Φ v := (lift.comp (P.galOfPlace s v).toAlgHom).1, mk_Φ := (galOfPlace ..).left_inv}

@[simp] lemma phi_algebraMap v x : Φ v (algebraMap P.K (P.E s) x) = x := by simp [Φ]

end Parameters

open Finset Fintype IsCoprime ZMod

/-- For a prime p dividing N, the cyclotomic polynomials over any commutative ring satisfy
Φ_N(X^{p^k}) = Φ_{Np^k}(X). -/
lemma Parameters.expand_pow_cyclotomic {p N} (h : p.Prime) (e : p ∣ N) k R [CommRing R] :
    expand R (p ^ k) (cyclotomic N R) = cyclotomic (N * p ^ k) R := by
  induction k <;> simp [*, pow_succ', expand_mul, e.mul_right]; ring

variable {P : Parameters} {s} {ν : ℤ}

lemma Parameters.expand_towerDeg_cyclotomic : expand ℂ (towerDeg s) (cyclotomic P.N₀ ℂ) =
  cyclotomic (P.N₁ s) ℂ := by erw [expand_mul, expand_pow_cyclotomic,
  expand_pow_cyclotomic] <;> norm_num <;> grind [Parameters, towerDeg]

/-- The number of infinite places of E is 3^c 2^s φ(N₀), where 3^c 2^s = `towerDeg` s and φ is
Euler's totient function. -/
lemma Parameters.card_infinitePlace_E s : numInfPlaces (P.E s) =
  towerDeg s * P.N₀.totient := by simp [mul_comm, card_congr (placeMulEquiv ..).1,
  ← natDegree_cyclotomic _ ℂ, ← expand_towerDeg_cyclotomic, natDegree_expand]

/-- Exactly N₁/N₀ = 3^c 2^s = `towerDeg` s infinite places of E, read as elements of (ℤ/N₁)^×,
are congruent to 1 modulo N₀. -/
lemma Parameters.card_placeClass_eq d : #{v | @placeClass P s P.N₀ d v = 1} = towerDeg
  s := by simpa [card_infinitePlace_E, ne, placeClass, Subgroup.index_ker, Fintype.card_subtype,
  unitsMap_surjective, ↓MonoidHom.mem_ker] using! (P.placeClass d).ker.card_mul_index

/-- The chosen element ζ of E is a primitive root of unity of order N₁ = 3^c 2^s N₀, where 3^c
2^s = `towerDeg` s. -/
lemma Parameters.isPrimitiveRoot_zeta : IsPrimitiveRoot (P.ζ s) (P.N₁ s) :=
  IsCyclotomicExtension.zeta_spec ..

lemma Parameters.phi_mul v v' x : Φ (v * v') x = Φ v (P.galOfPlace s v' x) := by simp [Φ]

@[simp] lemma Parameters.star_ζ : star (P.ζ s) = (P.ζ s)⁻¹ := (Φ 1).injective (by
  simp [Complex.inv_eq_conj, (isPrimitiveRoot_zeta.map_of_injective (Φ _).injective).norm'_eq_one,
    ne])

lemma Parameters.galOfPlace_zeta v : P.galOfPlace s v (P.ζ s) =
  P.ζ s ^ (P.placeClass dvd_rfl v).1.val := by simp [placeClass, placeMulEquiv, ζ]

/-- For every natural number s, the power 2^(s+1) divides N₁ = 3^c 2^s N₀. -/
lemma Parameters.two_pow_dvd_N₁ : 2 ^ (s + 1) ∣ P.N₁ s := by grind [Parameters, towerDeg,
  mul_dvd_mul, dvd_mul_left]

lemma Parameters.placeOfInt_pow i : P.placeOfInt s ν ^ i =
  P.placeOfInt s (ν ^ i) := by cases i <;> simp [placeOfInt, ← map_pow]; rfl

lemma Parameters.placeClass_placeOfInt (h : IsCoprime ν P.N₀) {m d} :
  (@placeClass P s m d (P.placeOfInt s ν)).1 = ν := by
  simp (disch := grind [Parameters, h.symm.of_isCoprime_of_dvd_left]) [placeClass, placeOfInt,
    unitsMap_val, towerDeg, coe_int_isUnit_iff_isCoprime, mul_left_iff, IsCoprime.pow_left, h.symm]

/-- For an integer ν prime to N₀, the element of Gal(E/K) attached to the infinite place named
by ν (`Parameters.placeOfInt`) sends the chosen primitive N₁-th root of unity ζ to ζ^ν. -/
lemma Parameters.galOfPlace_placeOfInt_zeta (h : IsCoprime ν P.N₀) :
  P.galOfPlace s (P.placeOfInt s ν) (P.ζ s) = P.ζ s ^ ν := by simp [galOfPlace_zeta,
  placeClass_placeOfInt h, ← zpow_natCast, coe_intCast, Int.emod_def, zpow_sub₀,
  isPrimitiveRoot_zeta.ne_zero out, (isPrimitiveRoot_zeta.zpow_eq_one_iff_dvd _).2]

/-- No power dⁿ, n ≥ 0, is congruent to −1 modulo N₀. -/
lemma Parameters.pow_d_ne_neg_one n : (P.d : ZMod P.N₀) ^ n ≠ -1 := by
  obtain ⟨⟨⟩⟩ := P.4.odd_iff.2 (by grind [lt_d]), P.5
  simp_all [← natCast_eq_zero_iff]
  induction n using Nat.twoStepInduction <;> grind

@[simp] lemma Parameters.placeClass_placeOfInt_eq_neg_one d :
  @placeClass P s P.N₀ d (P.placeOfInt s ν) = -1 ↔ (ν : ZMod P.N₀) = -1 := Units.ext_iff.trans
  ⟨by simp [placeOfInt, apply_dite, placeClass, unitsMap_val]; grind [P.pow_d_ne_neg_one 0], by
    simp_all [placeClass_placeOfInt (.symm _), ← coe_int_isUnit_iff_isCoprime]⟩

/-- For an automorphism σ of ℂ fixing K pointwise, the permutation of the infinite places of E given
by multiplication by the place of the embedding σ∘Φ₁. -/
def Parameters.placePerm {P} s (σ : Gal(ℂ/K P)) := Equiv.mulLeft (.mk (.comp σ (Φ 1)) : P.Φ s)

/-- Let σ be a ring automorphism of ℂ fixing K pointwise. For every infinite place v of E and x
∈ E, σ(Φ_v x) = Φ_{v'} x, where Φ_v is the chosen embedding at v and v' the image of v under
`Parameters.placePerm`. -/
lemma Parameters.placePerm_spec {P s σ} v x : σ (Φ v x) = Φ (@placePerm P s σ v) x := by
  simpa [placePerm,
    Φ] using! congr($(@algHom_eq_of_mk_eq P s _ (.comp σ ⟨Φ 1, by simp⟩) (mk_Φ _)) _).symm

end

variable {P s} {y : Parameters.E P s}

/-- Every root of unity y of E is a power ζ^k, k < N₁, of the chosen primitive N₁-th root of
unity ζ. -/
lemma Parameters.exists_zeta_pow_eq (h : IsOfFinOrder y) : ∃ k < P.N₁ s, ζ P s ^ k = y :=
  isPrimitiveRoot_zeta.eq_pow_of_pow_eq_one (by_contra (by grind [lt_d, by
  simpa [finrank_eq_two_mul_card_infinitePlace, Fintype.card_congr (placeMulEquiv ..).1, NeZero.pos,
    d_prime, Nat.totient_prime] using totient_mul_totient_le_finrank _ _ (coprime_N₁_d ..)
    isPrimitiveRoot_zeta <| .iff_orderOf.2 <| orderOf_eq_prime (pow_mul y .. ▸
    orderOf_dvd_iff_pow_eq_one.1 ((IsCyclotomicExtension.Rat.torsionOrder_eq.trans
      (ite_eq_left (by grind
    [Parameters]))).subst (@NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot _ _ _ ⟨by simpa⟩ _
    (.map_of_injective (.orderOf y) toCycloField.injective)))) ·]))

lemma Parameters.prod_phi_eq_norm : ∏ v, Φ v y = Algebra.norm P.K y := by
  simp [← phi_algebraMap _ s 1, Φ, Algebra.norm_eq_prod_automorphisms, ← (galOfPlace ..).prod_comp]

namespace Parameters

open Ideal Finset IntermediateField IsCyclotomicExtension NumberField Polynomial Algebra
  InfinitePlace RingOfIntegers NeZero QuadField algebraMap
variable {P s : _} {z : 𝓞 (E P s)}

/-- The chosen primitive N₁-th root of unity of E, regarded as an element of the ring of
integers of E. -/
abbrev zetaInt P s := (@isPrimitiveRoot_zeta P s).toInteger

@[simp] lemma coe_zetaInt : P.zetaInt s = P.ζ s := rfl

lemma isPrimitiveRoot_zetaInt : IsPrimitiveRoot (P.zetaInt s) (P.N₁ s) :=
  isPrimitiveRoot_zeta.toInteger_isPrimitiveRoot

/-- The image of c₀ = (1+√−d)/2 under the inclusion of the ring of integers of K into that of E. -/
abbrev c₀InE P s : 𝓞 (E P s) := c₀ P.d

/-- The element 2c₀ − 1 = √−d of the ring of integers of E. -/
def sqrtNegDInE P s := algebraMap _ (𝓞 (E P s)) (sqrtNegDInt P.d)

attribute [local simp] isPrimitiveRoot_zetaInt pos ne map_ofNat different_eq_span_and_adjoin_c₀
  prod_pow prod_nonneg sqrtNegDInE

@[simp] lemma coe_sqrtNegDInE : (P.sqrtNegDInE s).val = algebraMap _ _ (sqrtNegD P.d) :=
  congr(algebraMap P.K _ $(by simp [two_mul]))

lemma star_sqrtNegDInE : star (P.sqrtNegDInE s) = -P.sqrtNegDInE s :=
  ext (by simp [← map_star_CM, -sqrtNegDInE])

lemma star_zetaInt_pow_mul c : star (P.zetaInt s) ^ c * P.zetaInt s ^ c = 1 :=
  ext (by simp [isPrimitiveRoot_zeta.ne_zero])

lemma sqrtNegDInE_dvd :
  P.sqrtNegDInE s ∣ P.d := by simpa using congr(P.sqrtNegDInE s ∣ $(sqrtNegDInt_sq P.d))

lemma c₀InE_mul_one_sub P s : c₀InE P s * (1 - P.c₀InE s) = ↑((P.d + 1) / 4) := by
  simpa using congr(algebraMap _ (𝓞 _) $(c₀_mul_one_sub P.d))

lemma star_c₀InE P s :
  star (c₀InE P s) = 1 - P.c₀InE s := by grind [by simpa using @star_sqrtNegDInE P s]

instance : StablyUnram (P.E s) := ⟨_,
  isPrimitiveRoot_zeta.pow one_le (Nat.div_mul_cancel (by grw [N₁, ← P.3, towerDeg]; grind)).symm⟩

/-- Let z ∈ 𝓞_E be a primitive N₁-th root of unity and y the derivative of the N₁-th cyclotomic
polynomial at z. Then y divides N₁, y generates the different of E/K, and 𝓞_E = 𝓞_K[z]. -/
lemma relDifferent_spec (hz :
  IsPrimitiveRoot z (P.N₁ s)) : let y := (cyclotomic (P.N₁ s) _).derivative.eval z
  y ∣ P.N₁ s ∧ span {y} = differentIdeal (𝓞 P.K) _ ∧ (𝓞 P.K)[z] = ⊤ := by
  have hz' := hz.map_of_injective coe_injective
  have : IsCyclotomicExtension _ ℚ ℚ⟮_⟯ := hz'.intermediateField_adjoin_isCyclotomicExtension _
  have h := IsPrimitiveRoot.coe_submonoidClass_iff (ζ := AdjoinSimple.gen ℚ _).1 hz'
  rcases hz.isRoot_cyclotomic one_le, (cyclotomic_eq_minpoly h one_le).trans (minpoly_coe
    h.toInteger) ▸ conductor_mul_differentIdeal _ ℚ _ _ (adjoin_primitive_root_eq_top h),
    congr($((cyclotomic.dvd_X_pow_sub_one (P.N₁ s) _).choose_spec).derivative.eval z * z)
  refine ⟨?d, have := (coprime_N₁_d ..).symm.cast.mono sqrtNegDInE_dvd ?d; .imp_left .symm
    (differentIdeal_eq_span_of_dvd P.K (adjoin_primitive_root_eq_top hz') (cyclotomic (P.N₁ s)
      _) ?_ ?_ (.trans ?_ (IsDedekindDomain.map_differentIdeal_dvd_differentIdeal ℤ _ _ (𝓞 ℚ⟮z.val⟯)
      ?_)))⟩ <;> simp_all [isCoprime_span_singleton_iff, ← derivative_map, ← eval_map_apply, hz.1,
    ← eval_map_algebraMap, conductor_eq_top_of_adjoin_eq_top, Rat.adjoin_singleton_eq_top,
    derivative_pow, mul_assoc, pow_sub_one_mul, mem_span_singleton] <;> trivial

/-- The integer P'(ζ) of E, P the N₁-th cyclotomic polynomial and ζ the chosen root; it
generates the different of E/K. -/
abbrev relDifferentGen P s := (cyclotomic (N₁ P s) _).derivative.eval (P.zetaInt s)

lemma relDifferentGen_dvd_N₁ : P.relDifferentGen s ∣ P.N₁ s := by simp [↓relDifferent_spec]

@[simp↓] lemma relDifferentGen_ne_zero P s :
  (relDifferentGen P s).val ≠ 0 := mod_cast ne_zero_of_dvd_ne_zero out relDifferentGen_dvd_N₁

lemma different_eq_span_relDifferentGen_mul : differentIdeal ℤ _ =
  span {P.relDifferentGen s * P.sqrtNegDInE s} := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal _ (𝓞 P.K)]
  simp [← (relDifferent_spec isPrimitiveRoot_zetaInt).2, span_mul_span]

/-- The integer N₁d lies in the different of E over ℚ. -/
lemma cycloConductor_mem_different : ↑(P.N₁ s * P.d) ∈ differentIdeal ℤ (𝓞 (P.E s)) := by
  grw [Nat.cast_mul, different_eq_span_relDifferentGen_mul, mem_span_singleton,
    relDifferentGen_dvd_N₁, sqrtNegDInE_dvd]

lemma exists_unit_mul_relDifferentGen_real : ∃ c, star c * c = 1 ∧ star (c * P.relDifferentGen s) =
  c * P.relDifferentGen s := by
  rw [relDifferentGen, cyclotomic_eq_prod_X_sub_primitiveRoots isPrimitiveRoot_zetaInt,
    ← mul_prod_erase (a := zetaInt ..)]
  refine induction_on' (erase ..) ⟨1, ?_⟩ ?_ <;> simp [isPrimitiveRoot_zetaInt.isPrimitiveRoot_iff]
  rintro _ _ - l - h rfl - _ k _ _
  cases (h.of_dvd_right (by grind [Parameters])).odd_of_right
  use StablyUnram.exists_i_c₀.choose * k * star (zetaInt ..) ^ ‹ℕ›.succ
  repeat simp_all <;> grind [star_zetaInt_pow_mul, pow_mul']

/-- The integer ϖ_E = c·P'(ζ)·√−d of E, for a chosen c with c̄c = 1 and c·P'(ζ) real: a purely
imaginary generator of the different of E. -/
def ϖ P s :=
  (@exists_unit_mul_relDifferentGen_real P s).choose * (P.relDifferentGen s * P.sqrtNegDInE s)

/-- The integer ϖ_E = `Parameters.ϖ` of E is purely imaginary: its complex conjugate is −ϖ_E. -/
lemma star_ϖ : star (P.ϖ s) = -P.ϖ s := by grind [ϖ, star_mul, star_sqrtNegDInE]

/-- The different of E over ℚ is the principal ideal generated by ϖ_E (`Parameters.ϖ`). -/
lemma different_eq_span_varpi : differentIdeal ℤ _ = span {P.ϖ s} := by
  grind [ϖ, span_singleton_mul_left_unit, isUnit_iff_exists, different_eq_span_relDifferentGen_mul]

/-- The product of the absolute values of ϖ_E over the infinite places of E equals rd_E raised
to the number of infinite places, rd_E the root discriminant. -/
lemma prod_varpi_eq_rootDiscr_pow : ∏ v : P.Φ s, v (P.ϖ s).val =
  rootDiscr (P.E s) ^ numInfPlaces (P.E s) := by
  rcases congr(√$(prod_eq_abs_norm (P.ϖ s).val)), congr(√$(@different_eq_span_varpi P s).absNorm)
  simp_all [← coe_norm_int, absNorm_differentIdeal (P.E s), abs_discr_eq_rootDiscr_pow,
    (rootDiscr_pos _).le]

lemma infinitePlace_apply_varpi (v : P.Φ s) : v (P.ϖ s).val = v (P.relDifferentGen s) * √P.d :=
  mk_Φ v ▸ by simp [ϖ, -sqrtNegDInE, -mk_Φ, by
  simpa using congr(√‖Φ v $(exists_unit_mul_relDifferentGen_real.choose_spec.1).val‖)]
