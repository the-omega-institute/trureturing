import OmegaMath.NumberTheory.GRH.Lib.Adelic.Adeles.CoprimeValuation
import OmegaMath.NumberTheory.GRH.Lib.ClassField.Places.CyclotomicCharacter
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes
(known result; see Lib.ClassField.Places.LocalFrobenius).

This file: Places as valuation rings over primes: existence, conjugacy, finitely many ramified. -/

open NumberField IsDedekindDomain.HeightOneSpectrum Pointwise Ideal WithZero Valuation Nat
  IsScalarTower RingOfIntegers IsLocalRing Classical Algebra IsGaloisGroup
variable {K Ω Γ} [Field K] [Field Ω] [Algebra K Ω] [Group Γ] [MulSemiringAction Γ Ω]
  {A A' : ValuationSubring Ω} {w : Valuation K ℤᵐ⁰}


variable (A) in
lemma algebraMap_ringOfIntegers_mem (x : 𝓞 K) : algebraMap K Ω x ∈ A :=
  Subring.isIntegrallyClosedIn_iff.1 inferInstance x.2.algebraMap.tower_top

/-- The centre of the valuation subring A on K: the ideal of the elements of 𝓞_K whose image in
Ω lies in the maximal ideal of A. -/
def centrePrime K [Field K] [Algebra K Ω] A := (maximalIdeal _).comap
  (((algebraMap K Ω).comp _).codRestrict A (algebraMap_ringOfIntegers_mem A))

lemma mem_centrePrime {x} : x ∈ centrePrime K A ↔ valuationVia K A x < 1 := A.valuation_lt_one_iff _

instance {k} [Field k] [Algebra K k] [Algebra k Ω] [IsScalarTower K k Ω] : (A.valuation.comap <|
  algebraMap K _).HasExtension (A.valuation.comap (algebraMap k _)) := ⟨algebraMap_eq K k Ω ▸ .refl⟩

lemma isUniformiser_iff_of_isEquiv (h : (A.valuation.comap (algebraMap K Ω)).IsEquiv w) (hp : ∃ p,
  w p =
  exp (-1)) {π} : IsUniformiser A π ↔ w π = exp (-1) := (forall_congr' ((h.lt_one_iff_lt_one.trans
  (lt_mul_exp_iff_le (@exp_ne_zero _ (-1)))).iff <| h · π)).trans (by grind)


instance : (centrePrime K A).IsPrime := .comap _

variable [NumberField K] {v v' : FinPlace K} (h : IsPlaceOver A v) {L} [Field L]
  [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]

namespace IsPlaceOver

lemma of_le_centrePrime (h : v.1 ≤ centrePrime K A) : IsPlaceOver A v :=
  fun _ ↦ v.isMaximal.eq_of_le IsPrime.ne_top' h ▸ mem_centrePrime.symm

omit [NumberField K] in
lemma isPlaceOver_below {u : FinPlace L} (h : IsPlaceOver A u) : IsPlaceOver A (u.below K) :=
  (algebraMap_apply K L Ω · ▸ h (mapRingHom _ _))

include h

omit [NumberField K] in
lemma centrePrime_liesOver : (centrePrime Ω A).LiesOver v.1 :=
  ⟨(ext (mem_centrePrime.trans <| h ·)).symm⟩

/-- If the valuation subring A of Ω lies over the prime v of the number field K, then the
valuation of A restricted to K is equivalent to the v-adic valuation. -/
lemma isEquiv : (A.valuation.comap (algebraMap K Ω)).IsEquiv (v.valuation K) := by
  rw [isEquiv_iff_valuationSubring, ← valuationSubringAtPrime_eq_valuationSubring,
    (v.valuationSubringAtPrime K).eq_of_le_of_ne_top (fun _ ⟨_, _⟩ ↦ _) (v.3 ∘ _)] <;>
  simp_all [mul_mem, algebraMap_ringOfIntegers_mem, SetLike.ext_iff, ← map_inv₀,
    (h _).symm.trans A.mem_nonunits_iff_or]

lemma valuationVia_eq_one_iff {x} : valuationVia K A x = 1 ↔ v.valuation K x = 1 :=
  h.isEquiv.eq_one_iff_eq_one

section

omit [NumberField K]

lemma unique : IsPlaceOver A v' → v = v' :=
  (v.ext <| ·.centrePrime_liesOver.1 ▸ h.centrePrime_liesOver.1)

lemma valuation_natCast_lt_one_iff {n : ℕ} : A n < 1 ↔ ↑n ∈ v.1 := mod_cast h n

lemma valuation_natCast_eq_one_iff {n : ℕ} : A n = 1 ↔ ↑n ∉ v.1 := by simp [← h n, le_antisymm_iff]

end

lemma valuation_q_lt_one : A v.q < 1 := h.valuation_natCast_lt_one_iff.2 (absNorm_mem _)

lemma isUniformiser_iff {π} : IsUniformiser A π ↔ v.valuation K π = exp (-1) :=
  isUniformiser_iff_of_isEquiv h.isEquiv (valuation_exists_uniformizer ..)

omit [NumberField K] in
lemma smul [SMulCommClass Γ K Ω] (g : Γ) : IsPlaceOver (g • A) v := (by
  simp [← h ·, ← val_smul_lt_one g (A := A)])

end IsPlaceOver

lemma FinPlace.isPlaceOver_placeOver [Algebra K _root_.Ω] (v : FinPlace K) :
  IsPlaceOver (placeOver v) v := @epsilon_spec _
  (IsPlaceOver · _) ((exists_factor_valuationRing (algebraMap (v.valuationSubringAtPrime K) _)).imp
  fun _ ⟨_, ⟨h⟩⟩ ↦ .of_le_centrePrime fun _ ↦ (((maximalIdeal _).over_def _).le · <| h _ ·))

/-- For a prime p there is a place v of ℚ of norm p, with p a uniformiser at v and a unit
elsewhere, such that every valuation subring of Ω in whose maximal ideal p lies is over v. -/
lemma exists_rat_place_of_prime {p} (hp : Prime p) : ∃ v : FinPlace ℚ,
  (v.q = p ∧ ∀ w ≠ v, w.valuation ℚ p =
  1) ∧ v.valuation ℚ p = exp (-1) ∧ ∀ A : ClosurePlace, A.valuation p < 1 → IsPlaceOver A v :=
  have e : absNorm (span {(p : 𝓞 ℚ)}) = p := by simp [↓absNorm_span_natCast, rank]
  let v := ofPrime (irreducible_of_irreducible_absNorm (e ▸ hp :)).prime
  ⟨v, ⟨e, fun w n ↦ w.valuation_eq_one_iff_notMem.2 (w.prime.irreducible.1 ∘ (w.isCoprime_of_ne _
    n).isUnit_of_dvd ∘ dvd_span_singleton.2)⟩, (valuation_of_algebraMap ..).trans
    (v.intValuation_singleton (by aesop) rfl), fun _ ↦
    .of_le_centrePrime ∘ by simp [v, mem_centrePrime, valuationVia]⟩

variable [NumberField L] (K) [TopologicalSpace Γ] [G : IsProGalois Γ K Ω] [Algebra.IsAlgebraic K Ω]

instance : Algebra.IsAlgebraic (𝓞 K) Ω := IsFractionRing.comap_isAlgebraic_iff.2 ‹_›

instance : IsGaloisGroup Γ (𝓞 K) (𝓞 Ω) := have := (IsIntegralClosure.isFractionRing_of_algebraic
  (𝓞 K) (𝓞 Ω) (L := Ω) (by simp)); G.of_isFractionRing ..

lemma exists_isPlaceOver_of_val_ne_one {x} (a : x ≠ 0) (h : A x ≠ 1) : ∃ v : FinPlace K,
  IsPlaceOver A v := ⟨⟨centrePrime ..,
  .comap _, fun e ↦ transcendental_of_ne_one _ (hv := ⟨fun _ n ↦ (A.valuation_eq_one_iff _).1
  (by_contra (n <| e.le ·))⟩) x a h (IsAlgebraic.isAlgebraic x)⟩, .of_le_centrePrime le_rfl⟩

variable {K}

/-- For an open subgroup U of the Galois group Γ of Ω/K, only finitely many primes v of K have a
place above them whose inertia group is not contained in U. -/
lemma finite_ramified {U} (h : U.IsOpen) : ∀ᶠ v in .cofinite, ∀ A, @IsPlaceOver K Ω _ _ _ A v →
  inertiaGroup Γ A ≤ U := le_nhds_of_unique_clusterPt (l := .bind (.bind .cofinite (.principal ∘ _))
  (.principal ∘ _)) (fun g ↦ ((faithful (𝓞 K)).1 fun x : 𝓞 Ω ↦ by_contra fun n ↦ ·.frequently
  ((isLocallyConstant_smul ↑x).eventually_eq g) ((finite_factors ((span {g • x - x}).under_ne_bot _
  (by aesop))).eventually_cofinite_notMem.mono fun v k A a _ I e ↦ k (dvd_iff_le.2
  ((IsPlaceOver.centrePrime_liesOver a).1 ▸ comap_mono
  (by simpa [e, mem_centrePrime] using! I.2 x (by
                  simpa using algebraMap_ringOfIntegers_mem A x))))))) (h.mem_nhds U.one_mem)

variable (Γ)
include h

omit [Algebra.IsAlgebraic K Ω] in
lemma IsPlaceOver.exists_above [Algebra.IsAlgebraic L Ω] : ∃ u : FinPlace L, IsPlaceOver A u ∧
  u.below K = v := by grind [exists_isPlaceOver_of_val_ne_one L (by simp [↓map_ne_zero])
  ((h _).2 (absNorm_mem _)).ne, → isPlaceOver_below, unique]

/-- The Galois group Γ of Ω/K acts transitively on the valuation subrings of Ω lying over a
given prime v of K. -/
lemma IsPlaceOver.exists_smul (h' : IsPlaceOver A' v) : ∃ g : Γ, g • A = A' :=
  let : UniformSpace (𝓞 Ω) := ⊥
  have := continuousSMul_iff_stabilizer_isOpen.2 (Subgroup.isOpen_mono (fun _ ↦ (ext ·)) <| G.6 ·.1)
  (IsInvariant.exists_smul_of_under_eq_of_profinite _ _
    (h'.centrePrime_liesOver.1 ▸ h.centrePrime_liesOver.1)).imp' (·⁻¹) fun g e ↦ SetLike.ext
    fun x ↦ have ⟨_, o, _⟩ := h'.exists_above (L := fixedFieldOf (id (OpenSubgroup.mk _ (G.6 x))).1)
    by simpa using (isEquiv (A :=
      g⁻¹ • A) (by simpa [mem_centrePrime, ← o _, ← val_smul_lt_one g⁻¹ (A := A), algebraMap.smul']
      using! congr(g • algebraMap _ (𝓞 Ω) · ∈ $e))).trans o.isEquiv.symm ⟨x, (·.2)⟩ 1
