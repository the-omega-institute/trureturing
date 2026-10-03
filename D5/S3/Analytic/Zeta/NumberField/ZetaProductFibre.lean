/- GID: D5/S3/Analytic/Zeta/NumberField/ZetaProductFibre
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/NumberField/ZetaProductFibre
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A Frobenius ideal-fibre count decomposes into finite bad-part norm-residue counts. -/
module

public import D5.S3.Analytic.Zeta.NumberField.ZetaProductArithmetic

/-!
# Zeta factorisation for an abelian extension

The arithmetic and analytic estimates below assemble the Artin Euler
product, ideal-norm counts and nonvanishing argument.
-/

@[expose] public section

noncomputable section

open NumberField

namespace Chebotarev

open UniqueFactorizationMonoid

section GapBAssembly

/-- The cyclotomic character sends `frobeniusIdeal` of a coprime-norm ideal to its norm
residue: multiplicative extension of the per-prime native cyclotomic character formula over the
normalized factors. -/
private theorem autToPow_frobeniusIdeal
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L] [IsMulCommutative Gal(L/K)]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ m) (𝔠 : Ideal (𝓞 K)) (h𝔠 : 𝔠 ≠ ⊥)
    (hcop : (Ideal.absNorm 𝔠).Coprime m) :
    hζ.autToPow K (frobeniusIdeal K L 𝔠) = ZMod.unitOfCoprime (Ideal.absNorm 𝔠) hcop := by
  classical
  revert h𝔠 hcop
  induction 𝔠 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h𝔠 _ ↦ absurd rfl h𝔠
  | h₂ u hu =>
      intro _ hcop
      obtain rfl : u = ⊤ := Ideal.isUnit_iff.mp hu
      rw [(show ∀      
          [IsMulCommutative Gal(L/K)], frobeniusIdeal K L ⊤ = 1 from by
        intro attributeInstance0
        letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
        rw [frobeniusIdeal, ← Ideal.one_eq_top, UniqueFactorizationMonoid.normalizedFactors_one,
          Multiset.map_zero, Multiset.prod_zero]), map_one]
      exact Units.ext (by simp [ZMod.coe_unitOfCoprime])
  | h₃ a p ha hp ih =>
      intro hpa hcop
      have hp' : p ≠ ⊥ := hp.ne_zero
      have ha' : a ≠ ⊥ := ha
      haveI : p.IsPrime := Ideal.isPrime_of_prime hp
      have hsplit : Ideal.absNorm (p * a) = Ideal.absNorm p * Ideal.absNorm a :=
        map_mul Ideal.absNorm p a
      have hcp : (Ideal.absNorm p).Coprime m :=
        Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) (hsplit ▸ hcop)
      have hca : (Ideal.absNorm a).Coprime m :=
        Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ rfl) (hsplit ▸ hcop)
      rw [(show ∀      
          [IsMulCommutative Gal(L/K)] {𝔞 𝔟 : Ideal (𝓞 K)} (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥), (frobeniusIdeal K L (𝔞 * 𝔟) = frobeniusIdeal K L 𝔞 * frobeniusIdeal K L 𝔟) from by
        intro cnrInstance0 𝔞 𝔟 h𝔞 h𝔟
        classical
        letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
        rw [frobeniusIdeal, frobeniusIdeal, frobeniusIdeal,
          UniqueFactorizationMonoid.normalizedFactors_mul h𝔞 h𝔟, Multiset.map_add, Multiset.prod_add]) hp' ha', map_mul,
        (show ∀      
            [IsMulCommutative Gal(L/K)] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥), frobeniusIdeal K L 𝔭 = (frobeniusClass K L 𝔭).out from by
          intro attributeInstance0 𝔭 attributeInstance1 h𝔭
          letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
          rw [frobeniusIdeal, UniqueFactorizationMonoid.normalizedFactors_irreducible
            (Ideal.prime_of_isPrime h𝔭 ‹_›).irreducible, normalize_eq, Multiset.map_singleton,
            Multiset.prod_singleton]) p hp',
        (show ∀      
            (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
            {ζ : L} (hζ : IsPrimitiveRoot ζ m) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
            (hunr : UnramifiedIn K L 𝔭) (hcop : (Ideal.absNorm 𝔭).Coprime m), (hζ.autToPow K ((frobeniusClass K L 𝔭).out : L ≃ₐ[K] L) = ZMod.unitOfCoprime (Ideal.absNorm 𝔭) hcop) from by
          intro m cnrInstance0 cnrInstance1 ζ hζ 𝔭 cnrInstance2 hunr hcop
          obtain ⟨𝔓, h𝔓prime, hcomap⟩ :=
            Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔭 (by
              rw [(RingHom.injective_iff_ker_eq_bot _).mp
                (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))]
              exact bot_le)
          have h𝔓lo : 𝔓.LiesOver 𝔭 := ⟨hcomap.symm⟩
          haveI := h𝔓prime
          haveI := h𝔓lo
          haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
            (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓)
          set φ : L ≃ₐ[K] L := arithFrobAt (𝓞 K) Gal(L/K) 𝔓
          have hclass : frobeniusClass K L 𝔭 = ConjClasses.mk φ := by
            let e : ∃ 𝔓₀ : Ideal (𝓞 L), 𝔓₀.IsPrime ∧ 𝔓₀.LiesOver 𝔭 := by
              obtain ⟨𝔓₀, hp₀, hcomap₀⟩ :=
                Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔭 (by
                  rw [(RingHom.injective_iff_ker_eq_bot _).mp
                    (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))]
                  exact bot_le)
              exact ⟨𝔓₀, hp₀, ⟨hcomap₀.symm⟩⟩
            let 𝔓₀ := Classical.choose e
            haveI : 𝔓₀.IsPrime := (Classical.choose_spec e).1
            have hlo₀ : 𝔓₀.LiesOver 𝔭 := (Classical.choose_spec e).2
            haveI : Finite (𝓞 L ⧸ 𝔓₀) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓₀
              (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓₀)
            rw [frobeniusClass, dif_pos ⟨‹𝔭.IsPrime›, hunr⟩]
            change ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀) = ConjClasses.mk φ
            exact ConjClasses.mk_eq_mk_iff_isConj.mpr <|
              isConj_arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀ 𝔓 (hlo₀.over.symm.trans h𝔓lo.over)
          have hconj : IsConj ((frobeniusClass K L 𝔭).out) φ := by
            rw [← ConjClasses.mk_eq_mk_iff_isConj, ← hclass]
            change (⟦(frobeniusClass K L 𝔭 : Quotient (IsConj.setoid Gal(L/K))).out⟧ :
              Quotient (IsConj.setoid Gal(L/K))) = frobeniusClass K L 𝔭
            exact Quotient.out_eq _
          rw [isConj_iff_eq.mp ((hζ.autToPow K).map_isConj hconj)]
          have hact : φ ζ = ζ ^ Ideal.absNorm 𝔭 :=
            (show ∀      
                (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] (𝔭 : Ideal (𝓞 K))
                [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hcop : (Ideal.absNorm 𝔭).Coprime m)
                (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭), (haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓); ∀ ζ : L, ζ ∈ primitiveRoots m L → arithFrobAt (𝓞 K) Gal(L/K) 𝔓 ζ = ζ ^ Ideal.absNorm 𝔭) from by
              intro m cnrInstance0 cnrInstance1 𝔭 cnrInstance2 hunr hcop 𝔓 cnrInstance3 hP
              haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
                (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓)
              intro ζ hζmem
              set φ := arithFrobAt (𝓞 K) Gal(L/K) 𝔓
              have hζ : IsPrimitiveRoot ζ m := (mem_primitiveRoots (NeZero.pos m)).mp hζmem
              set z : 𝓞 L := hζ.toInteger
              have hzc : (algebraMap (𝓞 L) L) z = ζ := rfl
              have hzpow : z ^ m = 1 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
              set q := Ideal.absNorm 𝔭
              have h𝔭ne : 𝔭 ≠ ⊥ := (hunr).1
              have hcopP : (Ideal.absNorm 𝔓).Coprime m := by
                rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver 𝔓 𝔭 ‹𝔭.IsPrime› h𝔭ne]
                exact Nat.Coprime.pow_left _ hcop
              have hN1 : Ideal.absNorm 𝔓 ≠ 1 := fun h ↦ ‹𝔓.IsPrime›.ne_top (Ideal.absNorm_eq_one_iff.mp h)
              have hmnotmem : (m : 𝓞 L) ∉ 𝔓 := by
                intro hmem
                have hd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
                rw [Ideal.absNorm_span_singleton, show ((m : ℕ) : 𝓞 L) = algebraMap ℤ (𝓞 L) (m : ℤ) by
                    push_cast; rfl, Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at hd
                exact hN1 ((hcopP.pow_right _).eq_one_of_dvd hd)
              have hqcard : q = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K)) := by
                change Ideal.absNorm 𝔭 = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K))
                rw [show 𝔭 = 𝔓.under (𝓞 K) from Ideal.LiesOver.over (p := 𝔭) (P := 𝔓),
                  Ideal.absNorm_apply, Submodule.cardQuot_apply]
              have key := (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓).apply_of_pow_eq_one hzpow hmnotmem
              rw [← hqcard] at key
              have hmap := congrArg (algebraMap (𝓞 L) L) key
              rwa [map_pow,
                show (algebraMap (𝓞 L) L) ((MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) φ) z) = φ ζ from rfl,
                hzc] at hmap) m 𝔭 hunr hcop 𝔓 h𝔓lo ζ
              ((mem_primitiveRoots (NeZero.pos m)).mpr hζ)
          have hspec := hζ.autToPow_spec K φ
          rw [hact] at hspec
          apply Units.ext
          rw [ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val ((hζ.autToPow K φ : (ZMod m)ˣ) : ZMod m)]
          have hmod := (hζ.isOfFinOrder (NeZero.ne m)).pow_eq_pow_iff_modEq.mp hspec
          exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr
            (by simpa only [← hζ.eq_orderOf] using hmod)) m hζ p
          (unramifiedIn_of_coprime_absNorm K L m p hp' hcp) hcp,
        ih ha' hca]
      exact Units.ext (by push_cast [ZMod.coe_unitOfCoprime, hsplit]; ring)

open nonZeroDivisors in
/-- The good-fibre count is a norm-residue count: for `h : Gal(L/K)`, the ideals with norm
`≤ X`, norm coprime to `m`, and `frobeniusIdeal = h` are exactly the ideals with norm `≤ X`
and norm residue `(hζ.autToPow K h : ZMod m)` — coprimality and the unramified support come
for free from the residue being a unit, and the Frobenius condition is the residue condition
by injectivity of the cyclotomic character. -/
private theorem card_good_fibre_eq_card_residue
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L] [IsMulCommutative Gal(L/K)]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ m) (h : Gal(L/K)) (X : ℕ) :
    Nat.card {𝔠 : Ideal (𝓞 K) // 𝔠 ≠ ⊥ ∧ Ideal.absNorm 𝔠 ≤ X ∧
        (Ideal.absNorm 𝔠).Coprime m ∧ frobeniusIdeal K L 𝔠 = h}
      = Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ X ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m))
          = ((hζ.autToPow K h : (ZMod m)ˣ) : ZMod m)} := by
  classical
  refine Nat.card_congr
    { toFun := fun 𝔠 ↦ ⟨⟨𝔠.1, mem_nonZeroDivisors_of_ne_zero 𝔠.2.1⟩, 𝔠.2.2.1, by
        obtain ⟨𝔠, h0, hX, hcp, hfr⟩ := 𝔠
        subst hfr
        rw [autToPow_frobeniusIdeal K L m hζ 𝔠 h0 hcp, ZMod.coe_unitOfCoprime]⟩
      invFun := fun I ↦ ⟨(I.1 : Ideal (𝓞 K)), ?_⟩
      left_inv := fun 𝔠 ↦ Subtype.ext rfl
      right_inv := fun I ↦ Subtype.ext (Subtype.ext rfl) }
  have h0 : (I.1 : Ideal (𝓞 K)) ≠ ⊥ := by
    simpa using nonZeroDivisors.coe_ne_zero I.1
  have hcp : (Ideal.absNorm (I.1 : Ideal (𝓞 K))).Coprime m := by
    refine (ZMod.isUnit_iff_coprime _ m).mp ?_
    rw [I.2.2]
    exact (hζ.autToPow K h).isUnit
  have hfr : frobeniusIdeal K L (I.1 : Ideal (𝓞 K)) = h := by
    refine hζ.autToPow_injective (K := K) ?_
    rw [autToPow_frobeniusIdeal K L m hζ _ h0 hcp]
    exact Units.ext (by rw [ZMod.coe_unitOfCoprime, I.2.2])
  exact ⟨h0, I.2.1, hcp, hfr⟩

/-- The **bad part** of an ideal at level `m`: the product of its normalized prime factors
whose norm is not coprime to `m`. For an unramified-supported ideal these are the finitely
many factors lying over divisors of `m` that are unramified despite `𝔭 ∣ (m)`. -/
private noncomputable def badPart (K : Type*) [Field K] [NumberField K] (m : ℕ)
    (𝔞 : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  ((UniqueFactorizationMonoid.normalizedFactors 𝔞).filter
    fun 𝔭 ↦ ¬(Ideal.absNorm 𝔭).Coprime m).prod

/-- The **good part**: the product of the factors with norm coprime to `m`. -/
private noncomputable def goodPart (K : Type*) [Field K] [NumberField K] (m : ℕ)
    (𝔞 : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  ((UniqueFactorizationMonoid.normalizedFactors 𝔞).filter
    fun 𝔭 ↦ (Ideal.absNorm 𝔭).Coprime m).prod

section BadGoodSplit

variable (K : Type*) [Field K] [NumberField K] (m : ℕ)

end BadGoodSplit

end GapBAssembly

section FibrePartition

/-- **Per-bad-part fibre bijection (Sharifi 7.2.2 geometry-of-numbers step C).** Fix a nonzero,
"bad-supported" ideal `𝔟` (every factor unramified with norm *not* coprime to `m`) and a target
Frobenius `g`. The unramified-supported ideals `𝔞` of norm `≤ N` with `Frob 𝔞 = g` whose bad part
is exactly `𝔟` are in bijection with the *coprime-norm* ideals `𝔠` of norm `≤ ⌊N / N𝔟⌋` with
`Frob 𝔠 = g · (Frob 𝔟)⁻¹`, via `𝔞 ↦ goodPart 𝔞` (inverse `𝔠 ↦ 𝔠 * 𝔟`). The norm bound transfers
through `N(goodPart 𝔞) · N𝔟 = N𝔞` (`Nat.le_div_iff_mul_le`), the Frobenius condition through
multiplicativity and group cancellation, and the normalized-factor bad/good split. -/
private theorem card_fibre_eq_card_good_fibre
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (g : Gal(L/K)) (N : ℕ) {𝔟 : Ideal (𝓞 K)} (h𝔟 : 𝔟 ≠ ⊥)
    (hbU : ∀ 𝔭 ∈ normalizedFactors 𝔟, UnramifiedIn K L 𝔭)
    (hbn : ∀ 𝔭 ∈ normalizedFactors 𝔟, ¬(Ideal.absNorm 𝔭).Coprime m) :
    Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
          (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
            frobeniusIdeal K L 𝔞 = g ∧ badPart K m 𝔞 = 𝔟}
        = Nat.card {𝔠 : Ideal (𝓞 K) // 𝔠 ≠ ⊥ ∧ Ideal.absNorm 𝔠 ≤ N / Ideal.absNorm 𝔟 ∧
            (Ideal.absNorm 𝔠).Coprime m ∧ frobeniusIdeal K L 𝔠 = g * (frobeniusIdeal K L 𝔟)⁻¹} := by
  classical
  have hNb : 0 < Ideal.absNorm 𝔟 :=
    Nat.pos_of_ne_zero fun h ↦ h𝔟 (Ideal.absNorm_eq_zero_iff.mp h)
  refine Nat.card_congr
    { toFun := fun 𝔞 ↦ ⟨goodPart K m 𝔞.1, (Multiset.prod_ne_zero fun h0 ↦ (UniqueFactorizationMonoid.prime_of_normalized_factor _
      (Multiset.mem_of_mem_filter h0)).ne_zero rfl), ?_, ?_, ?_⟩
      invFun := fun 𝔠 ↦ ⟨𝔠.1 * 𝔟, ?_, ?_, ?_, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · obtain ⟨𝔞, h0, hN, _, _, hbad⟩ := 𝔞
    have hgood : goodPart K m 𝔞 * 𝔟 = 𝔞 := by
      rw [← hbad, goodPart, badPart, ← Multiset.prod_add, Multiset.filter_add_not]
      exact Ideal.prod_normalizedFactors_eq_self h0
    refine (Nat.le_div_iff_mul_le hNb).mpr ?_
    rw [← map_mul Ideal.absNorm, hgood]
    exact hN
  · exact (show ∀ (𝔞 : Ideal (𝓞 K)), ((Ideal.absNorm (goodPart K m 𝔞)).Coprime m) from by
    intro 𝔞
    rw [goodPart, map_multiset_prod]
    refine Multiset.prod_induction (fun n : ℕ ↦ n.Coprime m) _
      (fun a b ha hb ↦ Nat.Coprime.mul_left ha hb) (Nat.coprime_one_left m) fun n hn ↦ ?_
    obtain ⟨𝔭, h𝔭, rfl⟩ := Multiset.mem_map.mp hn
    exact (Multiset.mem_filter.mp h𝔭).2) 𝔞.1
  · obtain ⟨𝔞, h0, _, _, hfr, hbad⟩ := 𝔞
    have hgood : goodPart K m 𝔞 * 𝔟 = 𝔞 := by
      rw [← hbad, goodPart, badPart, ← Multiset.prod_add, Multiset.filter_add_not]
      exact Ideal.prod_normalizedFactors_eq_self h0
    refine eq_mul_inv_of_mul_eq ?_
    change frobeniusIdeal K L
      (((normalizedFactors 𝔞).filter fun 𝔭 ↦ (Ideal.absNorm 𝔭).Coprime m).prod) *
        frobeniusIdeal K L 𝔟 = g
    unfold goodPart at hgood
    rw [← (show ∀      
        [IsMulCommutative Gal(L/K)] {𝔞 𝔟 : Ideal (𝓞 K)} (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥), (frobeniusIdeal K L (𝔞 * 𝔟) = frobeniusIdeal K L 𝔞 * frobeniusIdeal K L 𝔟) from by
      intro cnrInstance0 𝔞 𝔟 h𝔞 h𝔟
      classical
      letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
      rw [frobeniusIdeal, frobeniusIdeal, frobeniusIdeal,
        UniqueFactorizationMonoid.normalizedFactors_mul h𝔞 h𝔟, Multiset.map_add, Multiset.prod_add]) ((Multiset.prod_ne_zero fun h0 ↦ (UniqueFactorizationMonoid.prime_of_normalized_factor _
      (Multiset.mem_of_mem_filter h0)).ne_zero rfl)) h𝔟, hgood, hfr]
  · exact mul_ne_zero 𝔠.2.1 h𝔟
  · obtain ⟨𝔠, h0, hN, _, _⟩ := 𝔠
    rw [map_mul Ideal.absNorm]
    exact (Nat.le_div_iff_mul_le hNb).mp hN
  · obtain ⟨𝔠, h0, _, hcop, _⟩ := 𝔠
    intro 𝔭 h𝔭
    rw [normalizedFactors_mul h0 h𝔟, Multiset.mem_add] at h𝔭
    rcases h𝔭 with h𝔭 | h𝔭
    · haveI : 𝔭.IsPrime := Ideal.isPrime_of_prime (prime_of_normalized_factor _ h𝔭)
      exact unramifiedIn_of_coprime_absNorm K L m 𝔭
        (prime_of_normalized_factor _ h𝔭).ne_zero
        ((show ∀ {𝔠 : Ideal (𝓞 K)}
            (hcop : (Ideal.absNorm 𝔠).Coprime m) {𝔮 : Ideal (𝓞 K)}
            (h𝔮 : 𝔮 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔠), ((Ideal.absNorm 𝔮).Coprime m) from by
          intro 𝔠 hcop 𝔮 h𝔮
          exact Nat.Coprime.coprime_dvd_left
            (Ideal.absNorm_dvd_absNorm_of_le
              (Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors h𝔮))) hcop) hcop h𝔭)
    · exact hbU 𝔭 h𝔭
  · obtain ⟨𝔠, h0, _, _, hfr⟩ := 𝔠
    rw [(show ∀      
        [IsMulCommutative Gal(L/K)] {𝔞 𝔟 : Ideal (𝓞 K)} (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥), (frobeniusIdeal K L (𝔞 * 𝔟) = frobeniusIdeal K L 𝔞 * frobeniusIdeal K L 𝔟) from by
      intro cnrInstance0 𝔞 𝔟 h𝔞 h𝔟
      classical
      letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
      rw [frobeniusIdeal, frobeniusIdeal, frobeniusIdeal,
        UniqueFactorizationMonoid.normalizedFactors_mul h𝔞 h𝔟, Multiset.map_add, Multiset.prod_add]) h0 h𝔟, hfr, inv_mul_cancel_right]
  · obtain ⟨𝔠, h0, _, hcop, _⟩ := 𝔠
    exact (show ∀ {𝔠 𝔟 : Ideal (𝓞 K)} (h𝔠 : 𝔠 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥)
        (hc : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔠, (Ideal.absNorm 𝔭).Coprime m)
        (hb : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔟, ¬(Ideal.absNorm 𝔭).Coprime m), (badPart K m (𝔠 * 𝔟) = 𝔟) from by
      intro 𝔠 𝔟 h𝔠 h𝔟 hc hb
      classical
      rw [badPart, UniqueFactorizationMonoid.normalizedFactors_mul h𝔠 h𝔟, Multiset.filter_add,
        Multiset.filter_eq_nil.mpr (fun 𝔭 h𝔭 ↦ not_not.mpr (hc 𝔭 h𝔭)),
        Multiset.filter_eq_self.mpr hb, zero_add]
      exact Ideal.prod_normalizedFactors_eq_self h𝔟) h0 h𝔟
      (fun 𝔭 h𝔭 ↦ (show ∀ {𝔠 : Ideal (𝓞 K)}
          (hcop : (Ideal.absNorm 𝔠).Coprime m) {𝔮 : Ideal (𝓞 K)}
          (h𝔮 : 𝔮 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔠), ((Ideal.absNorm 𝔮).Coprime m) from by
        intro 𝔠 hcop 𝔮 h𝔮
        exact Nat.Coprime.coprime_dvd_left
          (Ideal.absNorm_dvd_absNorm_of_le
            (Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors h𝔮))) hcop) hcop h𝔭) hbn
  · rintro ⟨𝔞, h0, _, _, _, hbad⟩
    apply Subtype.ext
    simp only
    rw [← hbad, goodPart, badPart, ← Multiset.prod_add, Multiset.filter_add_not]
    exact Ideal.prod_normalizedFactors_eq_self h0
  · rintro ⟨𝔠, h0, _, hcop, _⟩
    apply Subtype.ext
    simp only
    exact (show ∀ {𝔠 𝔟 : Ideal (𝓞 K)} (h𝔠 : 𝔠 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥)
        (hc : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔠, (Ideal.absNorm 𝔭).Coprime m)
        (hb : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔟, ¬(Ideal.absNorm 𝔭).Coprime m), (goodPart K m (𝔠 * 𝔟) = 𝔠) from by
      intro 𝔠 𝔟 h𝔠 h𝔟 hc hb
      classical
      rw [goodPart, UniqueFactorizationMonoid.normalizedFactors_mul h𝔠 h𝔟, Multiset.filter_add,
        Multiset.filter_eq_self.mpr hc, Multiset.filter_eq_nil.mpr hb, add_zero]
      exact Ideal.prod_normalizedFactors_eq_self h𝔠) h0 h𝔟
      (fun 𝔭 h𝔭 ↦ (show ∀ {𝔠 : Ideal (𝓞 K)}
          (hcop : (Ideal.absNorm 𝔠).Coprime m) {𝔮 : Ideal (𝓞 K)}
          (h𝔮 : 𝔮 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔠), ((Ideal.absNorm 𝔮).Coprime m) from by
        intro 𝔠 hcop 𝔮 h𝔮
        exact Nat.Coprime.coprime_dvd_left
          (Ideal.absNorm_dvd_absNorm_of_le
            (Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors h𝔮))) hcop) hcop h𝔭) hbn

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
  [IsCyclotomicExtension {m} K L]

/-- The "bad-supported" ideals of norm `≤ N`: nonzero, with every prime factor unramified in `L`
and of norm not coprime to `m`. -/
def IsBadPart (N : ℕ) (𝔟 : Ideal (𝓞 K)) : Prop :=
  𝔟 ≠ ⊥ ∧ (∀ 𝔭 ∈ normalizedFactors 𝔟, UnramifiedIn K L 𝔭 ∧ ¬(Ideal.absNorm 𝔭).Coprime m) ∧
    Ideal.absNorm 𝔟 ≤ N

/-- Ideals supported on unramified primes whose norm is not coprime to `m`, bounded by `N`. -/
noncomputable def badFinset (N : ℕ) : Finset (Ideal (𝓞 K)) :=
  (show {𝔟 : Ideal (𝓞 K) | IsBadPart K L m N 𝔟}.Finite from
    (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) N).subset
      (fun _ h𝔟 ↦ h𝔟.2.2)).toFinset

open UniqueFactorizationMonoid nonZeroDivisors in
/-- **The L2 count as a sum of norm-residue counts.** Chaining the finite bad-part partition, the per-bad-part bijection (`card_fibre_eq_card_good_fibre`), and the
good-fibre↔residue dictionary (`card_good_fibre_eq_card_residue`): the L2 fibre count at `g` is the
sum over the finite bad-part set of the norm-residue counts of modulus `m` at residue
`autToPow (g · Frob(𝔟)⁻¹)`, each up to norm `⌊N / N𝔟⌋`. -/
theorem card_L2_eq_sum_residue {ζ : L} (hζ : IsPrimitiveRoot ζ m) (g : Gal(L/K)) (N : ℕ) :
    Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
          (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ frobeniusIdeal K L 𝔞 = g}
        = ∑ 𝔟 ∈ badFinset K L m N,
          Nat.card {I : (Ideal (𝓞 K))⁰ //
            Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N / Ideal.absNorm 𝔟 ∧
              ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m))
                = ((hζ.autToPow K (g * (frobeniusIdeal K L 𝔟)⁻¹) : (ZMod m)ˣ) : ZMod m)} := by
  letI : Finite {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
      (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ frobeniusIdeal K L 𝔞 = g} := by
    haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ N} :=
      (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) N).to_subtype
    exact Finite.of_injective (β := {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ N})
      (fun 𝔞 ↦ ⟨𝔞.1, 𝔞.2.2.1⟩)
      (fun _ _ hab ↦ Subtype.ext (by simpa using hab))
  rw [(show ∀ (g : Gal(L/K)) (N : ℕ), (Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ frobeniusIdeal K L 𝔞 = g} = ∑ 𝔟 ∈ badFinset K L m N, Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧ (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ frobeniusIdeal K L 𝔞 = g ∧ badPart K m 𝔞 = 𝔟}) from by
    intro g N
    classical
    set L2 := {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
      (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ frobeniusIdeal K L 𝔞 = g}
    haveI : Finite L2 := by
      haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ N} :=
        (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) N).to_subtype
      exact Finite.of_injective (β := {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ N})
        (fun 𝔞 : L2 ↦ ⟨𝔞.1, 𝔞.2.2.1⟩)
        (fun _ _ hab ↦ Subtype.ext (by simpa using hab))
    have hbadmem : ∀ 𝔞 : L2, IsBadPart K L m N (badPart K m 𝔞.1) := by
      rintro ⟨𝔞, h0, hN, hU, _⟩
      refine ⟨(Multiset.prod_ne_zero fun h0 ↦ (UniqueFactorizationMonoid.prime_of_normalized_factor _
        (Multiset.mem_of_mem_filter h0)).ne_zero rfl), fun 𝔭 h𝔭 ↦ ?_, ?_⟩
      · exact ⟨hU 𝔭 ((show ∀ {𝔞 : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 K)}
          (h𝔭 : 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors (badPart K m 𝔞)), (𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞 ∧ ¬(Ideal.absNorm 𝔭).Coprime m) from by
        intro 𝔞 𝔭 h𝔭
        classical
        rw [badPart, UniqueFactorizationMonoid.normalizedFactors_prod_of_prime (fun 𝔮 h𝔮 ↦
          UniqueFactorizationMonoid.prime_of_normalized_factor _
            (Multiset.mem_of_mem_filter h𝔮))] at h𝔭
        exact ⟨Multiset.mem_of_mem_filter h𝔭, (Multiset.mem_filter.mp h𝔭).2⟩) h𝔭).1, ((show ∀ {𝔞 : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 K)}
            (h𝔭 : 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors (badPart K m 𝔞)), (𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞 ∧ ¬(Ideal.absNorm 𝔭).Coprime m) from by
          intro 𝔞 𝔭 h𝔭
          classical
          rw [badPart, UniqueFactorizationMonoid.normalizedFactors_prod_of_prime (fun 𝔮 h𝔮 ↦
            UniqueFactorizationMonoid.prime_of_normalized_factor _
              (Multiset.mem_of_mem_filter h𝔮))] at h𝔭
          exact ⟨Multiset.mem_of_mem_filter h𝔭, (Multiset.mem_filter.mp h𝔭).2⟩) h𝔭).2⟩
      · have hdvd : badPart K m 𝔞 ∣ 𝔞 := by
          rw [badPart]
          conv_rhs => rw [← Ideal.prod_normalizedFactors_eq_self h0]
          exact Multiset.prod_dvd_prod_of_le (Multiset.filter_le _ _)
        exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero
          (fun h ↦ h0 (Ideal.absNorm_eq_zero_iff.mp h)))
          (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd))) hN
    set F : L2 → badFinset K L m N :=
      fun 𝔞 ↦ ⟨badPart K m 𝔞.1, by
        simpa only [badFinset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hbadmem 𝔞⟩
    letI : ∀ a : badFinset K L m N, Finite {x : L2 // F x = a} :=
      fun _ ↦ Finite.of_injective Subtype.val Subtype.val_injective
    rw [Nat.card_congr (Equiv.sigmaFiberEquiv F).symm, Nat.card_sigma,
      ← Finset.sum_coe_sort (badFinset K L m N)]
    refine Finset.sum_congr rfl fun 𝔟 _ ↦ ?_
    refine Nat.card_congr
      { toFun := fun x ↦ ⟨x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2.1, x.1.2.2.2.2,
          Subtype.ext_iff.mp x.2⟩
        invFun := fun y ↦ ⟨⟨y.1, y.2.1, y.2.2.1, y.2.2.2.1, y.2.2.2.2.1⟩,
          Subtype.ext y.2.2.2.2.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }) g N]
  refine Finset.sum_congr rfl fun 𝔟 h𝔟 ↦ ?_
  rw [badFinset, Set.Finite.mem_toFinset] at h𝔟
  obtain ⟨h0, hbfac, _⟩ := h𝔟
  rw [card_fibre_eq_card_good_fibre K L m g N h0 (fun 𝔭 h ↦ (hbfac 𝔭 h).1)
      (fun 𝔭 h ↦ (hbfac 𝔭 h).2),
    card_good_fibre_eq_card_residue K L m hζ (g * (frobeniusIdeal K L 𝔟)⁻¹) (N / Ideal.absNorm 𝔟)]

end FibrePartition

end Chebotarev
