/- GID: D5/S3/Zeros/GRH/Lib/ClassField/Places/CyclotomicCharacter
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/Places/CyclotomicCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.Places.CyclotomicCharacter. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/Places/CyclotomicCharacter.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.Places.ProfiniteGalois
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes
(known result; see Lib.ClassField.Places.LocalFrobenius).

This file: Basic properties of decomposition groups, inertia groups and Frobenius elements.
Cyclotomic characters: values on Frobenius and inertia; continuity, surjectivity. -/

open Function HasEnoughRootsOfUnity IntermediateField IsCyclotomicExtension MonoidHom NeZero
  PadicInt Subgroup Units ZMod rootsOfUnity

attribute [local simp↓] mul_smul mem_decompGroup_iff

variable {Γ Ω} [Group Γ] [Field Ω] [MulSemiringAction Γ Ω] {A : ValuationSubring Ω} {σ : Γ} {K}
  [Field K] [Algebra K Ω] [TopologicalSpace Γ] [IsProGalois Γ K Ω] (x : Ω) {N : ℕ} {x y : Ω}

instance isClosed_decompGroup : IsClosed (decompGroup Γ A : Set Γ) := Eq.subst (by aesop)
    (isClosed_iInter (isClosed_setOf_smul · (· ∈ A ↔ _)))

include K in
/-- For Γ the Galois group of Ω/K, an element σ of the decomposition group of A preserves the
valuation of A: σx and x have the same valuation for every x in Ω. -/
lemma decompGroup.val_smul (h : σ ∈ decompGroup Γ A) x : A (σ • x) = A x :=
  have (s : decompGroup Γ A) x := (Set.exists_min_image _ A (isLocallyConstant_smul x).range_finite
    ⟨_, s, rfl⟩).elim fun _ ⟨⟨t, e⟩, H⟩ ↦ ((A.valuation.comap (MulSemiringAction.toRingHom
    ..)).isEquiv_of_val_le_one (by simpa using t.2) ..).1 (e ▸ H _ ⟨t * s, mul_smul ..⟩)
  ((this ⟨_, inv_mem h⟩ _).trans (by simp)).antisymm (this ⟨_, h⟩ x)

instance isClosed_inertiaGroup : IsClosed (inertiaGroup Γ A : Set Γ) := isClosed_decompGroup.and
    (Set.ofPred_forall _ ▸ isClosed_iInter (isClosed_setOf_smul · (_ → · - _ ∈ A.nonunits)))

/-- Let A be a valuation subring of a field Ω and x, y in Ω with x^N = y^N = 1. If the
multiplicative A-valuation of x − y is strictly smaller than that of N, then x = y. -/
lemma eq_of_pow_eq_one_of_val_sub_lt (hx : x ^ N = 1) (hy : y ^ N = 1) (h :
  A.valuation (x - y) < A.valuation N) : x = y := by
  lift y to A using by simpa [pow_le_one_iff (by aesop : N ≠ 0)] using congr(A $hy).le
  cases h.le; cases sq_dvd_add_pow_sub_sub (‹A› * N) y N.succ; contrapose! h
  use -‹A›; simp_all [Subtype.ext_iff, A.smul_def]; grind

lemma eq_of_val_sub_lt_one (hN : A N = 1) (hx : x ^ N = 1) (hy : y ^ N = 1) :
    A (x - y) < 1 → x = y := hN ▸ eq_of_pow_eq_one_of_val_sub_lt hx hy

variable {Γ Ω : Type*} [Group Γ] [Field Ω] [MulSemiringAction Γ Ω] {N q : ℕ} {σ g : Γ}
  {A : ValuationSubring Ω} (h : IsFrob A q σ) (hN : A N = 1) {ζ : Ω} [IsAlgClosed Ω] [CharZero Ω]
  [NeZero N] {a M : ℕ} [NeZero M] {l : ℕ} [Fact (Nat.Prime l)] {Γ' Ω'} [Group Γ'] [Field Ω']
  [MulSemiringAction Γ' Ω'] [IsAlgClosed Ω'] [CharZero Ω'] {j : Ω →+* Ω'} {g' : Γ'} {K : Type*}
  [Field K]

lemma cycCharMod_spec (g : Γ) (h : ζ ^ N = 1) : g • ζ = ζ ^ (cycCharMod Ω N g).1.val :=
  modularCyclotomicCharacter.spec Ω _ _ (mkOfPowEq ζ h).2 ▸ rfl

lemma cycCharMod_eq_of_isPrimitiveRoot (h : IsPrimitiveRoot ζ N) (e : g • ζ = ζ ^ a) :
  (cycCharMod Ω N g).1 = a := val_injective
  N (by grind [h.pow_inj, cycCharMod_spec, pow_eq_pow_mod, val_natCast, h.1])

lemma cycCharMod_eq_iff : (cycCharMod Ω N g).1 = a ↔ ∀ ζ : Ω, ζ ^ N = 1 → g • ζ = ζ ^ a := by
  grind [→ cycCharMod_spec g, pow_eq_pow_mod, val_natCast, @prim Ω,
    cycCharMod_eq_of_isPrimitiveRoot, IsPrimitiveRoot]

lemma cycCharMod_eq_of_dvd : M ∣ N → (cycCharMod Ω N g).1 = a → (cycCharMod Ω M g).1 = a := by
  simp_all [cycCharMod_eq_iff, pow_mul, dvd_def]

lemma cycCharMod_eq_one_of_dvd : M ∣ N → cycCharMod Ω N g = 1 →
  cycCharMod Ω M g = 1 := by simpa using cycCharMod_eq_of_dvd (a := 1)

lemma cycCharMod_eq_iff_unitsRep : (cycCharMod Ω N g).1 = a ↔ ∀ ⦃u : DiscreteUnits Ω⦄, N • u = 0 →
  unitsRep g u = a • u :=
  cycCharMod_eq_iff.trans ⟨(Units.ext ∘ · ·.1 ∘ val_inj.2), (val_inj.2 <| · <| mkOfPowEq · · |>.2)⟩

lemma cycCharMod_eq_one_iff : cycCharMod Ω N g = 1 ↔ ∀ y : DiscreteUnits Ω, N • y = 0 →
  unitsRep g y = y := by simpa using cycCharMod_eq_iff_unitsRep (a := 1)

include h hN in
lemma IsFrob.cycCharMod_eq :
  (_root_.cycCharMod Ω N σ).1 = q := cycCharMod_eq_iff.2 fun _ _ ↦ by apply eq_of_val_sub_lt_one hN
  <;> simp_all [h.2, ← smul_pow', pow_right_comm, ← map_pow, ← pow_le_one_iff (ne N)]

include h hN in
/-- Let Ω be algebraically closed of characteristic 0, N ≥ 1 a unit of A, and σ stabilise A with
σx ≡ x^q on A. Then σ fixes the N-th roots of unity if and only if q ≡ 1 mod N. -/
lemma IsFrob.mem_ker_cycCharMod_iff : σ ∈ (_root_.cycCharMod Ω N).ker ↔ q ≡ 1 [MOD N] := by
    simp_all [← h.cycCharMod_eq, ← natCast_eq_natCast_iff]

lemma cycCharMod_of_mem_inertiaGroup : σ ∈ inertiaGroup Γ A → A N = 1 → cycCharMod Ω N σ = 1 :=
  (·.mem_ker_cycCharMod_iff · |>.2 rfl)

lemma zmod_eq_natCast_val {g : ZMod N} : g = g.val := by simp

lemma map_cycCharMod_mul (μ : _ →+ DiscreteUnits Ω) (g : Γ) a :
    μ ((cycCharMod Ω N g).1 * a) = unitsRep g
  (μ a) := by simp [cycCharMod_eq_iff_unitsRep.1 (@zmod_eq_natCast_val N ..), ← map_nsmul]

lemma cycCharMod_prime_pow_eq r : cycCharMod (Γ := Γ) Ω _ = (Units.map (toZModPow r).1).comp
  (cycChar Ω l) := by ext; symm; apply cyclotomicCharacter.toZModPow

lemma pow_dvd_cycChar_sub_iff r : l.cast ^ r ∣ (cycChar Ω l σ).1 - q ↔ (cycCharMod Ω (l ^ r) σ).1 =
  q := by simp [← Ideal.mem_span_singleton, ← ker_toZModPow, cycCharMod_prime_pow_eq]

/-- Let Ω be algebraically closed of characteristic 0, A a ℤ_l-module and f : A → B additive
with image killed by l^r. Then f(χ_l(σ)x) = χ_{l^r}(σ)·f(x), with χ_l the l-adic and χ_{l^r}
the mod l^r cyclotomic character. -/
lemma map_cycChar_smul {A B} [AddCommGroup A] [Module ℤ_[l] A] [AddCommGroup B] (f : A →+ B) r (h :
  ∀ x, l ^ r • f x = 0) x : f ((cycChar Ω l σ).1 • x) = (cycCharMod Ω (l ^ r) σ).1.val • f x := by
  rw [eq_add_of_sub_eq ((pow_dvd_cycChar_sub_iff r).2 zmod_eq_natCast_val).choose_spec, add_smul,
    mul_smul]
  norm_cast; grind

variable (l)

lemma IsFrob.cycChar_eq (h : IsFrob A q σ) : A l = 1 → (_root_.cycChar Ω l σ).1 = q := by
  simp_all [← ext_of_toZModPow, ← h.cycCharMod_eq, cycCharMod_prime_pow_eq]

lemma cycChar_of_mem_inertiaGroup : σ ∈ inertiaGroup Γ A → A l = 1 → cycChar Ω l σ = 1 :=
  (Units.ext ∘ ·.cycChar_eq _)

lemma cycCharMod_eq_of_equivariant (e : ∀ x, j (g • x) = g' • j x) : cycCharMod Ω N g =
  cycCharMod Ω' N g' := Units.ext (.trans (cycCharMod_eq_iff.2 fun ζ _ ↦
  j.injective (by grind [cycCharMod_spec, =_ map_pow])) zmod_eq_natCast_val.symm)

lemma cycChar_eq_of_equivariant (e : ∀ x, j (g • x) = g' • j x) : cycChar Ω l g = cycChar Ω' l
  g' := by simpa [cycCharMod_prime_pow_eq, ext_of_toZModPow, ← val_inj] using fun r : ℕ ↦
  cycCharMod_eq_of_equivariant e (N := l ^ r)

omit [IsAlgClosed Ω] [CharZero Ω] in
lemma continuous_cycChar [Algebra K Ω] [TopologicalSpace Γ] [G : IsProGalois Γ K Ω] :
    Continuous (cycChar (Γ := Γ) Ω l) := (cyclotomicCharacter.continuous l K Ω).comp
    (continuous_of_equivariant_emb (φ := MulSemiringAction.toAlgAut ..) 1)

instance isOpen_ker_cycCharMod [Algebra K Ω] [TopologicalSpace Γ] [G : IsProGalois Γ K Ω] :
    Fact (cycCharMod (Γ := Γ) Ω N).ker.IsOpen := ⟨isOpen_mono
  (fun _ ↦ by simpa using cycCharMod_eq_of_isPrimitiveRoot (a := 1) prim.choose_spec) (G.6 _)⟩

variable (Ω N)

/-- A chosen injective homomorphism ℤ/N → Ω^× (written additively) with image the N-th roots of
unity, together with the proof of these properties. -/
noncomputable def rootPowHom : {f : ZMod N →+ DiscreteUnits Ω // Injective f ∧ ∀ y, y ∈ f.range ↔ N
  • y = 0} := have h := prim.choose_spec.isUnit_unit out; ⟨lift N ⟨zmultiplesHom _ (IsUnit.unit _),
  h.zpow_eq_one⟩, Subtype.val_injective.comp h.zmodEquivZPowers.injective,
  by simpa [intCast_surjective.exists, SetLike.ext_iff] using! h.zpowers_eq⟩

lemma isPrimitiveRoot_rootPowHom_one : IsPrimitiveRoot ((rootPowHom Ω N).1 1).toMul N :=
  .iff_orderOf.2 ((addOrderOf_injective _ (rootPowHom ..).2.1 1).trans (by simp))

/-- The subgroup of Gal(ℚ̄/ℚ) fixing all N-th roots of unity: the absolute Galois group of
ℚ(ζ_N). -/
noncomputable abbrev cycloGalGroup : Subgroup Gal(_root_.Ω/ℚ) := (cycCharMod _root_.Ω N).ker

/-- The cyclotomic field ℚ(ζ_N) inside ℚ̄, defined as the fixed field of `cycloGalGroup` N. -/
noncomputable abbrev cycloField := fixedFieldOf (cycloGalGroup N)

instance : IsCyclotomicExtension {N} ℚ (cycloField N) := by
  rw [cycloField, (_ : cycloGalGroup N = _), fixedFieldOf_fixingSubgroup]
  apply isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot; simp [prim]; ext
  erw [mem_fixingSubgroup_iff, forall_mem_adjoin_smul_eq_self_iff]
  simpa [ne] using! cycCharMod_eq_iff (a := 1)

lemma cycCharMod_surjective : Surjective (cycCharMod (Γ := Gal(_root_.Ω/ℚ)) _root_.Ω N) := by
  simp [← range_eq_top, eq_top_of_card_eq, ↓← index_ker, ← finrank_fixedFieldOf, Rat.finrank N]
