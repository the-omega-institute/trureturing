import GRH.Lib.ClassField.Places.SelmerDefs
import GRH.Lib.ClassField.Global.Avatars
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes
(known result; see Lib.ClassField.Places.LocalFrobenius).

Part of: Algebraic Hecke characters (type A₀); extension of the quadratic character of a CM field
(known result; see Lib.ClassField.HeckeCharacter.SplittingCharExists).

This file: Complex conjugation on Galois group, places, Frobenius, inertia; anticyclotomic
characters locally. -/


variable {ℓ} [ThePrime ℓ] {E : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]
  {A : ClosurePlace} {v : FinPlace E} (b : Bool) (g : Gal(Ω/E))

@[simp, grind =] lemma star_mem_placesDividing {T} : star v ∈ placesDividing E T ↔
  v ∈ placesDividing E T := by simp [placesDividing]

/-- The element g if b is true, and g^{−c} = (g^c)⁻¹ if b is false. -/
noncomputable def idOrConjInv := cond b g (conjGal g)⁻¹

@[simp] lemma conjGal_conjGal : conjGal (conjGal g) = g := by ext; simp [conjGal]

lemma cmConj_conjGal_smul x : cmConj.toRingHom (conjGal g • x) = g • cmConj.toRingHom x :=
  cmConj_cmConj _

@[fun_prop] lemma continuous_conjGal : Continuous (conjGal (E := E)) :=
  continuous_of_equivariant_emb _ cmConj_conjGal_smul

@[simp] lemma cycChar_conjGal : cycChar Ω ℓ (conjGal g) = cycChar Ω ℓ g :=
  cycChar_eq_of_equivariant ℓ (cmConj_conjGal_smul g)

/-- For a CM field E: if the Artin symbol of the finite idele x is the class of g, then that of
the conjugate idele x̄ is the class of g^c. -/
lemma artinMap_star {x} (h : artinMap Gal(Ω/E) x = g) : artinMap Gal(Ω/E) (star x) = conjGal g := by
  let := (starRingEnd E).toAlgebra
  convert ← artinMap_adeleNorm (star_star x ▸ h) _ cmConj_algebraMap (cmConj_conjGal_smul g)
  ext1; erw [Units.coe_map, adeleNorm_finAdeleIncl,
    Module.finrank_of_bijective_algebraMap starMulAut.bijective, pow_one]

/-- The conjugate place: the preimage of the valuation subring A of Ω under the chosen complex
conjugation. -/
noncomputable def conjPlace (A : ClosurePlace) := A.comap cmConj.toRingHom

variable {g}

@[simp] lemma conjPlace_conjPlace : conjPlace (conjPlace A) = A := by ext; simp [conjPlace]

/-- Let E be a CM field. If the valuation subring A of Ω lies over the finite place v of E, then
the conjugate place of A under the chosen complex conjugation lies over the conjugate prime
v̄. -/
lemma IsPlaceOver.conjPlace_star (h : IsPlaceOver A v) : IsPlaceOver (conjPlace A) (star v) :=
  fun _ ↦ val_comap_lt_one.trans (by simp [← h _])

lemma IsFrob.conjPlace_conjGal {q} : IsFrob A q g → IsFrob (conjPlace A) q (conjGal g) :=
  map cmConj_conjGal_smul

/-- Let E be a CM field, g in Gal(Ω/E) and c the chosen complex conjugation. Then g^c = cgc lies
in the inertia group of the conjugate place of A if and only if g lies in the inertia group
of A. -/
@[simp] lemma conjGal_mem_inertiaGroup_iff : conjGal g ∈ inertiaGroup _ (conjPlace A) ↔
  g ∈ inertiaGroup _ A := ⟨(by simpa using! ·.conjPlace_conjGal), .conjPlace_conjGal⟩

omit [NumberField.IsCMField E] in
lemma cycChar_eq_one_of_mem_inertiaAbove : g ∈ inertiaAbove (placesDividing E ℓ)ᶜ →
  cycChar Ω ℓ g = 1 := by grind [inertiaAbove, cycChar_of_mem_inertiaGroup,
  IsPlaceOver.valuation_natCast_eq_one_iff, placesDividing]

variable {C} [CommMonoid C] {S I} {χ : Gal(Ω/E) →* C} (h : IsFromU1 S I χ)
include h

/-- A character χ coming from U(1) in the sense of `IsFromU1` has χ(g^{−c}) = χ(g), where g^{−c}
= (g^c)⁻¹; stated for both values of `idOrConjInv`. -/
lemma IsFromU1.apply_idOrConjInv g : χ (idOrConjInv b g) = χ g := h.2.elim fun _ ⟨_, _, e⟩ ↦
  (artinMap_surjective ..).elim fun x k ↦ b.rec (by rw [e x g k,
  e (star x⁻¹)] <;> simp [idOrConjInv, inv_mul_eq_div, artinMap_star _ k]) rfl

/-- If χ satisfies `IsFromU1` for S and I (anticyclotomic of modulus I), then χ is trivial on
the decomposition group of every place A of Ω lying over a place v in S. -/
lemma IsFromU1.eq_one_of_mem_decompGroup (a : v ∈ S) (hA : IsPlaceOver A v) (c :
  g ∈ decompGroup _ A) : χ g = 1 := by
  obtain ⟨⟨φ, -, b, e⟩, x, s, hs, E⟩ := h.2, hA.denseRange_localArtin.exists_mem_open
    (QuotientGroup.isOpenMap_coe _ (h.1 _).preimage_val) ⟨_, ⟨g, c⟩, rfl, rfl⟩
  rw [hs, e (locIdele v x), b] <;> simp +contextual (disch := grind [star_star]) [idelesUnitOff,
    hA.artinAt_eq_of_localArtin_eq E.symm, star_locIdele]

/-- If χ satisfies `IsFromU1` for S and I (anticyclotomic of modulus I), then χ is unramified
off I ∪ Ī: χ(g) = 1 for g in any inertia group above a finite place of E outside I and its
conjugate. -/
lemma IsFromU1.eq_one_of_mem_inertiaAbove g : g ∈ inertiaAbove I.conjClosureᶜ → χ g = 1 :=
  fun ⟨v, _, A, a, c⟩ ↦ by
  obtain ⟨⟨φ, -, b, e⟩, x, k, E⟩ := h.2, a.exists_localArtin_eq (inv_mem c) 0
  rw [e (locIdele v x), star_locIdele, b _ (by simp [div_mem, ↓locIdele_mem_idelesUnitOff, *])] <;>
    simp +contextual (disch := grind) [a.artinAt_eq_of_localArtin_eq E]
