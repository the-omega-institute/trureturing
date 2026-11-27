/- GID: D5/S3/Zeros/GRH/Lib/ClassField/GaloisCohomology/TameCocycles
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/GaloisCohomology/TameCocycles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.GaloisCohomology.TameCocycles. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/GaloisCohomology/TameCocycles.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.GreenbergWiles.SelmerMembership
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Galois cohomology in degrees ≤ 2: Shapiro, Hilbert 90, Kummer, symbols, Herbrand
quotient (known result; see Lib.ClassField.GaloisCohomology.CyclicNorm).

Part of: Local Tate duality in degree 1, as an upper bound for orthogonal groups of cocycles (known
result; see Lib.ClassField.LocalDuality.CrystallineDuality).

Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes (known
result; see Lib.ClassField.Places.LocalFrobenius).

This file: Tame cocycles are determined by a tame generator and Frobenius; local length bound. -/


open Equiv.Perm Matrix Module MulAction LinearMap
variable {ℓ E O n} [Field E] [EmbeddedNumberField E] [CommRing O] [Fintype n] {ρ : Gal(Ω/E) →*
  Matrix n n O} {L} {A : ClosurePlace} {B} [AddCommGroup B] [Module O B] {M} (hB : ∀ b : B,
  ℓ ^ M • b = 0) {P : FinPlace E} (hA : IsPlaceOver A P) {c : _ → n → B} (hc : ∀ g h, c (g * h) =
  c g + ρ g • c h) {m} (hm : ∀ i ∈ inertiaGroup _ A, ρ (i ^ m) = 1) (ho : ∀ᶠ g in nhds 1, g ∈
  inertiaGroup _ A → ρ g = 1) (γ : inertiaGroup Gal(Ω/E) A) (hq : A.valuation (m * ℓ ^ M : ℕ) = 1)

variable (ρ L A B) in
/-- The restrictions to the decomposition group of A of the continuous cocycles of Gal(Ω over E)
for ρ with values in B^n that obey the relations L. -/
noncomputable def localCocycles :=
  (selmerModule ρ .univ L B).map (funLeft O _ (decompGroup _ A).subtype)

attribute [local simp] Equiv.ext_iff Units.smul_def coe_pow

/-- The affine action attached to a cocycle c: the homomorphism sending g to the permutation v ↦
c(g) + ρ(g)v of B^n. -/
noncomputable def affineAction := MonoidHom.mk' (fun g ↦
  .addLeft (c g) * toPerm (ρ.toHomUnits g)) (by simp [*, mul_smul, add_assoc])

include hc in
lemma cocycle_apply_inv g :
  c g⁻¹ = -(ρ g⁻¹ • c g) := by simpa [eq_neg_iff_add_eq_zero, ← hc] using hc 1 1

include hA hB hm ho hq

/-- Let ℓ^M kill B, ρ kill m-th powers of inertia and inertia near 1, q = mℓ^M be a unit at A, c
a locally constant cocycle, γ inertial. If c kills the tame generator, c(γ) = 0; in the
affine action γ commutes with Frobenii of exponent ≡ 1 mod q. -/
lemma tame_affineAction (hl : IsLocallyConstant c) : (c hA.tameGenerator = 0 → c γ = 0) ∧ ∀ ⦃k⦄,
  k ≡ 1 [MOD m * ℓ ^ M] → ∀ φ, IsFrob A k φ → Commute (affineAction hc φ) (affineAction hc γ) :=
  (fun K ↦ (hA.tame_inertia (affineAction hc) ((hl.eventually_eq 1).mp
  (ho.mono (by simp_all [← (affineAction hc).map_one, affineAction]))) hq K γ).imp
  (fun ⟨a, H⟩ z ↦ by simpa [affineAction, z, Function.iterate_fixed] using congr($H 0)) fun F k
  e ↦ by simpa [pow_eq_pow_of_modEq e, K, mul_inv_eq_iff_eq_mul, commute_iff_eq] using F k)
  (by simp_all [↓pow_mul, ↓← map_pow, affineAction, Function.comp_def, funext_iff])

/-- Let ℓ^M kill B, m-th powers of inertia and inertia near 1 act trivially, and mℓ^M be a unit
at A. Then `localCocycles` has length at most that of B^n plus that of ker(ρ(γ) − 1) on
B^n, for any inertial γ. -/
lemma length_localCocycles_le : length O (localCocycles ρ L A B) ≤ length O (n →
  B) + length O (ker ((ρ γ - 1) • 1 : End O (n → B))) := (hA.exists_isFrob _).rec fun φ hφ ↦ by
  grw [← relLength_add_length_inf _ (proj ⟨_, hA.tameGenerator.2.1⟩).ker, relLength_ker,
    length_mono le_top, length_top, ← relLength_bot, relLength_le_of_inj (proj ⟨φ, hφ.1⟩),
    relLength_bot] <;> rintro _ ⟨⟨y, Y, rfl⟩, h⟩ <;> have C := (mem_selmerModule_iff.1
    Y).1 <;> have Z := (tame_affineAction hB hA C hm ho ⟨·, ·⟩ hq Y.2 |>.1 h)
  exacts [by simpa [*, sub_smul] using (Z _ (.inv_mul (by simpa) (γ.2.mul_iff.2 hφ)) ▸ C φ _ :),
    funext ∘ (hA.decompGroup_le hφ (U := cocycleKer _ C) (Y.2 {0}) Z · ·.2)]

omit hm ho hq

/-- Let γ be the tame generator at A over P ∤ ℓ, ρ unramified at v = P or P̄, ℓ^M B = 0. For σ'
= σ or σ^{−c}, Selmer cocycles killing γ' are unramified at v, and vanish on a decomposition
group if they also kill φ', φ a Frobenius at A. -/
lemma exists_conj_side_detects [NumberField.IsCMField E] {γ} (t : ↑hA.tameGenerator = γ) {v} (l :
  P ∉ placesDividing E ℓ) (u : ∀ g ∈ inertiaAbove {v}, ρ g = 1) (hv : v = P ∨ v = star P) : ∃ b A',
  IsPlaceOver (Ω := Ω) A' v ∧ ∀ {S L}, ∀ c ∈
  selmerModule ρ S L B, c (idOrConjInv b γ) = 0 → (∀ g ∈ inertiaAbove {v}, c g = 0) ∧ ∀ φ,
  IsFrob A P.q φ → c (idOrConjInv b φ) = 0 → ∀ g : decompGroup _ A', c g.1 = 0 := by
  have T θ {c} C u j g := (tame_affineAction hB hA (ρ := ρ.comp θ) (c := c) C (m := 1) (by simpa)
    (.of_forall u) g (by simp [hA.valuation_natCast_eq_one_iff.2 l]) j).1
  simp_rw [mem_selmerModule_iff, ← t]
  obtain rfl | ⟨hA, rfl⟩ := hv.imp_right (And.intro hA.conjPlace_star) <;> refine ⟨?_, _, hA,
    fun c ⟨C, _, _, j⟩ z ↦ (fun H ↦ ⟨fun g ⟨_, rfl, _, b, i⟩ ↦ (b.exists_smul _ hA).rec fun s k ↦ by
    simpa [*, mul_assoc] using (H (k ▸ i.conj s) ▸ C s⁻¹ _ :), fun φ f k ↦
    (hA.decompGroup_le ?_ (j {0}) H (?_ : ?_ ∈ cocycleKer _ C) ·.2)⟩) ?_⟩
  exacts [true, (T (.id _) C (u · ⟨_, rfl, _, hA, ·⟩) j ⟨·, ·⟩ z), f, k, false, (conjGal_conjGal · ▸
    T conjGal (by simp [C]) (fun _ ↦ (u _ ⟨_, rfl, _, hA, ·.conjPlace_conjGal⟩))
    (j.comp_continuous (by fun_prop)) ⟨_, @conjPlace_conjPlace A ▸ ·.conjPlace_conjGal⟩
    ((cocycleKer _ C).inv_mem z)), by simpa using f.conjPlace_conjGal, inv_mem_iff.1 k]
