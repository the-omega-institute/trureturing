/- GID: D5/S3/Analytic/Zeta/NumberField/ZetaProductL2
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/NumberField/ZetaProductL2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cyclotomic Frobenius ideal fibres share a leading count constant and power error. -/
module

public import D5.S3.Analytic.Zeta.NumberField.ZetaProductFibre

@[expose] public section

noncomputable section

open NumberField Polynomial Finset UniqueFactorizationMonoid

namespace Chebotarev

section L2Assembly

/-! ### The κ-uniformity input: realizing the cyclotomic-character image as norm residues

To apply the ICC κ-uniform count (`exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`) we
must produce its Fourier-decay hypothesis `hF`, which the ICC producer
`tendsto_sum_char_mul_cardNormLeResidue_div_of_realized` derives from the **realizer hypothesis**
`hS`: every element of the residue subgroup `S` is the norm residue `(N𝔟 mod m)` of some nonzero
ideal `𝔟`. We take `S = range (autToPow)` (the image of the cyclotomic character) and prove `hS` via
the coprime-restricted Frobenii-generation theorem
`subgroup_eq_top_of_forall_frobenius_mem_of_coprime`
(CNR): the set `R` of realized residues is a subgroup, and its `autToPow`-preimage contains the
Frobenius of every coprime-norm unramified prime (native cyclotomic character formula), hence is `⊤`, so
every `autToPow`-value is realized. -/

open nonZeroDivisors in
/-- The **realized-residue subgroup** `R ≤ (ℤ/m)ˣ`: the residues `a` that are the norm residue
`(N𝔟 mod m)` of some nonzero ideal `𝔟` of `𝓞 K`. A genuine subgroup: `1` is realized by `⊤`
(`N⊤ = 1`), products by ideal products (`absNorm_mul`), and inverses by the finite-order power
`𝔟^{ord a − 1}` (so `N(𝔟^{ord a − 1}) ↦ a^{ord a − 1} = a⁻¹`). -/
private noncomputable def realizedResidues (K : Type*) [Field K] [NumberField K] (m : ℕ)
    [NeZero m] : Subgroup (ZMod m)ˣ where
  carrier := {a : (ZMod m)ˣ | ∃ 𝔟 : (Ideal (𝓞 K))⁰,
    ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod m)) = (a : ZMod m)}
  one_mem' := ⟨1, by
    rw [Submonoid.coe_one, Ideal.one_eq_top, Ideal.absNorm_top, Nat.cast_one, Units.val_one]⟩
  mul_mem' := by
    rintro a b ⟨𝔟₁, h₁⟩ ⟨𝔟₂, h₂⟩
    exact ⟨𝔟₁ * 𝔟₂, by rw [Submonoid.coe_mul, map_mul, Nat.cast_mul, h₁, h₂, Units.val_mul]⟩
  inv_mem' := by
    rintro a ⟨𝔟, h⟩
    refine ⟨𝔟 ^ (orderOf a - 1), ?_⟩
    have hpow : ((𝔟 ^ (orderOf a - 1) : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
        = (𝔟 : Ideal (𝓞 K)) ^ (orderOf a - 1) := by push_cast; ring
    have hinv : a⁻¹ = a ^ (orderOf a - 1) := inv_eq_of_mul_eq_one_right
      (by rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one])
    rw [hpow, map_pow, Nat.cast_pow, h, hinv, Units.val_pow_eq_pow_val]

open nonZeroDivisors in
/-- **Every cyclotomic-character value is a realized norm residue.** The image
`range (hζ.autToPow K)` is contained in the realized-residue subgroup `realizedResidues K m`:
applying the coprime-restricted Frobenii-generation
`subgroup_eq_top_of_forall_frobenius_mem_of_coprime`
to `H = comap (autToPow) R` (which contains every coprime-norm unramified prime's Frobenius, since
native cyclotomic character formula realizes it as `N𝔭 mod m` with the prime `𝔭` itself as the realizer)
forces `H = ⊤`, i.e. every `autToPow`-value lies in `R`. -/
private theorem autToPow_range_le_realizedResidues
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ m) :
    (hζ.autToPow K).range ≤ realizedResidues K m := by
  set R := realizedResidues K m with hR
  set H := Subgroup.comap (hζ.autToPow K) R with hH
  have hHtop : H = ⊤ := by
    refine subgroup_eq_top_of_forall_frobenius_mem_of_coprime K L m H
      (fun 𝔭 h𝔭p h𝔭ne h𝔭unr h𝔭cop ↦ ?_)
    haveI := h𝔭p
    rw [hH, Subgroup.mem_comap, (show ∀      
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
        (by simpa only [← hζ.eq_orderOf] using hmod)) m hζ 𝔭 h𝔭unr h𝔭cop]
    exact ⟨⟨𝔭, mem_nonZeroDivisors_of_ne_zero h𝔭ne⟩, by rw [ZMod.coe_unitOfCoprime]⟩
  intro a ha
  obtain ⟨g, rfl⟩ := ha
  have : g ∈ H := hHtop ▸ Subgroup.mem_top g
  rwa [hH, Subgroup.mem_comap] at this

/-! ### The bad-part Euler tail bound

The L2 error assembly sums per-bad-part residue counts over the finite bad-part set. The error
control reduces to bounding `∑_{𝔟 ∈ badFinset N} (N𝔟)^e` for a negative real exponent `e`, uniformly
in `N`. Since every bad-supported `𝔟` factors as `∏_{𝔭 ∈ P} 𝔭^{e_𝔭}` over the **fixed finite**
bad-prime set `P`, the sum injects into the exponent vectors
`P → {0,…,⌊log₂ N⌋}`
and the product-of-sums expansion (`Finset.prod_sum`) bounds it by the convergent geometric Euler
product `∏_{𝔭 ∈ P} (1 − (N𝔭)^e)⁻¹` (each factor `< 1` since `N𝔭 ≥ 2` and `e < 0`). -/

/-- **The bad-part Euler bound** (negative-exponent geometry-of-numbers tail). For a finite set `P`
of nonzero primes and a finite set `BF` of ideals each nonzero, supported on `P`
(`∀ 𝔭 ∈ normalizedFactors 𝔟, 𝔭 ∈ P`), and of norm `≤ N`, if every `(N𝔭)^e < 1` (`𝔭 ∈ P`), then
`∑_{𝔟 ∈ BF} (N𝔟)^e ≤ ∏_{𝔭 ∈ P} (1 − (N𝔭)^e)⁻¹`. Proof: each `𝔟 = ∏_{𝔭 ∈ P} 𝔭^{count 𝔭}`
(`Ideal.prod_normalizedFactors_eq_self` + `Finset.prod_multiset_count`), so `(N𝔟)^e =
∏_{𝔭} ((N𝔭)^e)^{count 𝔭}`; the count map `𝔟 ↦ (count 𝔭)_{𝔭 ∈ P}` is injective into the bounded
exponent vectors (`count 𝔭 ≤ ⌊log₂ N⌋` since `𝔭^{count} ∣ 𝔟` and `N𝔭 ≥ 2`), and `Finset.prod_sum`
turns `∏_𝔭 ∑_{k ≤ ⌊log₂ N⌋} ((N𝔭)^e)^k` into a sum over those vectors dominating the `BF`-sum; the
geometric partial sum is `≤ (1 − (N𝔭)^e)⁻¹` (`geom_sum_mul`). -/
private theorem sum_rpow_le_euler_prod (K : Type*) [Field K] [NumberField K]
    (P : Finset (Ideal (𝓞 K))) (hPprime : ∀ 𝔭 ∈ P, 𝔭.IsPrime ∧ 𝔭 ≠ ⊥)
    (N : ℕ) (BF : Finset (Ideal (𝓞 K)))
    (hBF : ∀ 𝔟 ∈ BF, 𝔟 ≠ ⊥ ∧
      (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔟, 𝔭 ∈ P) ∧ Ideal.absNorm 𝔟 ≤ N)
    (e : ℝ) (hxlt : ∀ 𝔭 ∈ P, ((Ideal.absNorm 𝔭 : ℝ)) ^ e < 1) :
    ∑ 𝔟 ∈ BF, ((Ideal.absNorm 𝔟 : ℝ)) ^ e
      ≤ ∏ 𝔭 ∈ P, (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e)⁻¹ := by
  classical
  set Kn := Nat.log 2 N with hKn
  have hx0 : ∀ 𝔭 ∈ P, (0 : ℝ) ≤ ((Ideal.absNorm 𝔭 : ℝ)) ^ e :=
    fun 𝔭 _ ↦ Real.rpow_nonneg (by positivity) e
  set cnt : Ideal (𝓞 K) → ((𝔭 : Ideal (𝓞 K)) → 𝔭 ∈ P → ℕ) :=
    fun 𝔟 𝔭 _ ↦ (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭 with hcnt
  set F : ((𝔭 : Ideal (𝓞 K)) → 𝔭 ∈ P → ℕ) → ℝ :=
    fun g ↦ ∏ 𝔭 ∈ P.attach, (((Ideal.absNorm 𝔭.1 : ℝ)) ^ e) ^ (g 𝔭.1 𝔭.2) with hF
  have hterm : ∀ 𝔟 ∈ BF, ((Ideal.absNorm 𝔟 : ℝ)) ^ e = F (cnt 𝔟) := by
    intro 𝔟 h𝔟
    obtain ⟨hb0, hbP, _⟩ := hBF 𝔟 h𝔟
    simpa only [hF, hcnt] using (show ∀ (P : Finset (Ideal (𝓞 K))) {𝔟 : Ideal (𝓞 K)} (h0 : 𝔟 ≠ ⊥) (hP : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔟, 𝔭 ∈ P) (e : ℝ), ((Ideal.absNorm 𝔟 : ℝ) ^ e = ∏ 𝔭 ∈ P.attach, (((Ideal.absNorm 𝔭.1 : ℝ)) ^ e) ^ (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭.1) from by
      intro P 𝔟 h0 hP e
      classical
      have hNprod : Ideal.absNorm 𝔟 =
          ∏ 𝔭 ∈ P, (Ideal.absNorm 𝔭) ^ (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭 := by
        conv_lhs => rw [(show ∀ (P : Finset (Ideal (𝓞 K))) {𝔠 : Ideal (𝓞 K)} (h0 : 𝔠 ≠ ⊥) (hP : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔠, 𝔭 ∈ P), (𝔠 = ∏ 𝔭 ∈ P, 𝔭 ^ (UniqueFactorizationMonoid.normalizedFactors 𝔠).count 𝔭) from by
          intro P 𝔠 h0 hP
          classical
          conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self h0]
          rw [Finset.prod_multiset_count]
          refine Finset.prod_subset (fun 𝔭 h ↦ hP 𝔭 (Multiset.mem_toFinset.mp h)) ?_
          intro 𝔭 _ hnotin
          rw [Multiset.count_eq_zero.mpr (fun h ↦ hnotin (Multiset.mem_toFinset.mpr h)), pow_zero]) P h0 hP, map_prod]
        exact Finset.prod_congr rfl fun 𝔭 _ ↦ by rw [map_pow]
      rw [Finset.prod_attach P
        (fun 𝔭 ↦ (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^
          (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭), hNprod]
      push_cast
      rw [← Real.finsetProd_rpow P _ (fun 𝔭 _ ↦ by positivity) e]
      refine Finset.prod_congr rfl fun 𝔭 _ ↦ ?_
      rw [← Real.rpow_natCast ((Ideal.absNorm 𝔭 : ℝ)) _,
        ← Real.rpow_natCast (((Ideal.absNorm 𝔭 : ℝ)) ^ e) _,
        ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity), mul_comm]) P hb0 hbP e
  have hmaps : ∀ 𝔟 ∈ BF, cnt 𝔟 ∈ P.pi (fun _ ↦ Finset.range (Kn + 1)) := by
    intro 𝔟 h𝔟
    obtain ⟨hb0, hbP, hbN⟩ := hBF 𝔟 h𝔟
    rw [Finset.mem_pi]; intro 𝔭 h𝔭
    rw [hcnt]; simp only; rw [Finset.mem_range, Nat.lt_succ_iff]
    obtain ⟨h𝔭p, h𝔭0⟩ := hPprime 𝔭 h𝔭
    exact (show ∀ {𝔭 𝔟 : Ideal (𝓞 K)} (h𝔭p : 𝔭.IsPrime) (h𝔭0 : 𝔭 ≠ ⊥) (hb0 : 𝔟 ≠ ⊥) {N : ℕ} (hbN : Ideal.absNorm 𝔟 ≤ N), ((UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭 ≤ Nat.log 2 N) from by
      intro 𝔭 𝔟 h𝔭p h𝔭0 hb0 N hbN
      classical
      have hk : 𝔭 ^ (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭 ∣ 𝔟 := by
        have hd := (show ∀ (a : (Ideal (𝓞 K))) (s : Multiset (Ideal (𝓞 K))), (a ^ s.count a ∣ s.prod) from by
          intro a s
          classical
          exact
            (Multiset.prod_replicate (s.count a) a) ▸
              Multiset.prod_dvd_prod_of_le (Multiset.le_count_iff_replicate_le.mp le_rfl)) 𝔭 (UniqueFactorizationMonoid.normalizedFactors 𝔟)
        rwa [Ideal.prod_normalizedFactors_eq_self hb0] at hd
      have hN𝔭2 : 2 ≤ Ideal.absNorm 𝔭 := by
        have h1 : Ideal.absNorm 𝔭 ≠ 1 := fun h ↦ h𝔭p.ne_top (Ideal.absNorm_eq_one_iff.mp h)
        have h0 : Ideal.absNorm 𝔭 ≠ 0 := fun h ↦ h𝔭0 (Ideal.absNorm_eq_zero_iff.mp h)
        omega
      have hb0' : Ideal.absNorm 𝔟 ≠ 0 := fun h ↦ hb0 (Ideal.absNorm_eq_zero_iff.mp h)
      have hdvd : Ideal.absNorm 𝔭 ^ (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭
          ∣ Ideal.absNorm 𝔟 := by
        have := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hk); rwa [map_pow] at this
      exact Nat.le_log_of_pow_le (by norm_num) (le_trans (Nat.pow_le_pow_left hN𝔭2 _)
        (le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hb0') hdvd) hbN))) h𝔭p h𝔭0 hb0 hbN
  have hinj : Set.InjOn cnt BF := by
    intro 𝔞 ha 𝔟 hb hcnteq
    obtain ⟨ha0, haP, _⟩ := hBF 𝔞 ha
    obtain ⟨hb0, hbP, _⟩ := hBF 𝔟 hb
    have hcc : ∀ 𝔭 ∈ P, (UniqueFactorizationMonoid.normalizedFactors 𝔞).count 𝔭
        = (UniqueFactorizationMonoid.normalizedFactors 𝔟).count 𝔭 :=
      fun 𝔭 h𝔭 ↦ congrFun (congrFun hcnteq 𝔭) h𝔭
    rw [(show ∀ (P : Finset (Ideal (𝓞 K))) {𝔠 : Ideal (𝓞 K)} (h0 : 𝔠 ≠ ⊥) (hP : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔠, 𝔭 ∈ P), (𝔠 = ∏ 𝔭 ∈ P, 𝔭 ^ (UniqueFactorizationMonoid.normalizedFactors 𝔠).count 𝔭) from by
      intro P 𝔠 h0 hP
      classical
      conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self h0]
      rw [Finset.prod_multiset_count]
      refine Finset.prod_subset (fun 𝔭 h ↦ hP 𝔭 (Multiset.mem_toFinset.mp h)) ?_
      intro 𝔭 _ hnotin
      rw [Multiset.count_eq_zero.mpr (fun h ↦ hnotin (Multiset.mem_toFinset.mpr h)), pow_zero]) P ha0 haP,
      (show ∀ (P : Finset (Ideal (𝓞 K))) {𝔠 : Ideal (𝓞 K)} (h0 : 𝔠 ≠ ⊥) (hP : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔠, 𝔭 ∈ P), (𝔠 = ∏ 𝔭 ∈ P, 𝔭 ^ (UniqueFactorizationMonoid.normalizedFactors 𝔠).count 𝔭) from by
        intro P 𝔠 h0 hP
        classical
        conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self h0]
        rw [Finset.prod_multiset_count]
        refine Finset.prod_subset (fun 𝔭 h ↦ hP 𝔭 (Multiset.mem_toFinset.mp h)) ?_
        intro 𝔭 _ hnotin
        rw [Multiset.count_eq_zero.mpr (fun h ↦ hnotin (Multiset.mem_toFinset.mpr h)), pow_zero]) P hb0 hbP]
    exact Finset.prod_congr rfl fun 𝔭 h𝔭 ↦ by rw [hcc 𝔭 h𝔭]
  calc ∑ 𝔟 ∈ BF, ((Ideal.absNorm 𝔟 : ℝ)) ^ e
      = ∑ 𝔟 ∈ BF, F (cnt 𝔟) := Finset.sum_congr rfl hterm
    _ = ∑ g ∈ BF.image cnt, F g := (Finset.sum_image (fun a ha b hb ↦ hinj ha hb)).symm
    _ ≤ ∑ g ∈ P.pi (fun _ ↦ Finset.range (Kn + 1)), F g := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun g _ _ ↦
          Finset.prod_nonneg fun 𝔭 _ ↦ pow_nonneg (hx0 𝔭.1 𝔭.2) _)
        intro g hg
        rw [Finset.mem_image] at hg
        obtain ⟨𝔟, h𝔟, rfl⟩ := hg
        exact hmaps 𝔟 h𝔟
    _ = ∏ 𝔭 ∈ P, ∑ k ∈ Finset.range (Kn + 1), (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ k := by
        rw [Finset.prod_sum P (fun _ ↦ Finset.range (Kn + 1))
          (fun 𝔭 k ↦ (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ k)]
    _ ≤ ∏ 𝔭 ∈ P, (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e)⁻¹ := by
        refine Finset.prod_le_prod₀
          (fun 𝔭 h𝔭 ↦ Finset.sum_nonneg fun k _ ↦ pow_nonneg (hx0 𝔭 h𝔭) k) (fun 𝔭 h𝔭 ↦ ?_)
        have h1x : 0 < 1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e := by have := hxlt 𝔭 h𝔭; linarith
        have hkey := geom_sum_mul (((Ideal.absNorm 𝔭 : ℝ)) ^ e) (Kn + 1)
        have hxK : (0 : ℝ) ≤ (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ (Kn + 1) := pow_nonneg (hx0 𝔭 h𝔭) _
        have hmul : (∑ k ∈ Finset.range (Kn + 1), (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ k)
            * (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e)
            = 1 - (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ (Kn + 1) := by nlinarith [hkey]
        have hle : (∑ k ∈ Finset.range (Kn + 1), (((Ideal.absNorm 𝔭 : ℝ)) ^ e) ^ k)
            * (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e) ≤ 1 := by rw [hmul]; linarith
        rw [← le_div_iff₀ h1x] at hle; rwa [one_div] at hle

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
  [IsCyclotomicExtension {m} K L]

omit [NumberField L] [FiniteDimensional K L] [IsMulCommutative Gal(L/K)]
  [IsCyclotomicExtension {m} K L] in
/-- The bad-part Euler bound specialised to `BF = badFinset N`, `P = badPrimes`: for a negative
exponent `e` (more precisely `(N𝔭)^e < 1` on the finite bad-prime set), the bad-part norm sum is
bounded by the geometric Euler product over the bad primes, **uniformly in `N`**. -/
private theorem sum_rpow_badFinset_le
    (hbad : {𝔭 : Ideal (𝓞 K) |
      𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ (Ideal.absNorm 𝔭).Coprime m}.Finite)
    (N : ℕ) (e : ℝ)
    (hxlt : ∀ 𝔭 ∈ hbad.toFinset, ((Ideal.absNorm 𝔭 : ℝ)) ^ e < 1) :
    ∑ 𝔟 ∈ (badFinset K L m N), ((Ideal.absNorm 𝔟 : ℝ)) ^ e
      ≤ ∏ 𝔭 ∈ hbad.toFinset, (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e)⁻¹ := by
  refine sum_rpow_le_euler_prod K hbad.toFinset (fun 𝔭 h𝔭 ↦ ?_) N _
    (fun 𝔟 h𝔟 ↦ ?_) e hxlt
  · rw [Set.Finite.mem_toFinset] at h𝔭; exact ⟨h𝔭.1, h𝔭.2.1⟩
  · rw [badFinset, Set.Finite.mem_toFinset] at h𝔟
    refine ⟨h𝔟.1, fun 𝔭 h𝔭 ↦ ?_, h𝔟.2.2⟩
    have hprime := prime_of_normalized_factor 𝔭 h𝔭
    rw [Set.Finite.mem_toFinset]
    exact ⟨Ideal.isPrime_of_prime hprime, hprime.ne_zero, (h𝔟.2.1 𝔭 h𝔭).2⟩

open nonZeroDivisors in
/-- **The bad-part inverse-norm tail bound.** With `e₂ = 1/d − 1 < 0`, the bad-part partial sum
`T_N = ∑_{𝔟 ∈ badFinset N} (N𝔟)⁻¹` converges to `T = ⨆_N T_N` with tail
`T − T_N ≤ N^{−1/d}·E₂`, where `E₂` bounds the `e₂`-Euler sum (`hEuler`). On the difference set
`badFinset M ∖ badFinset N` (`N ≤ M`) each `N𝔟 > N`, so `(N𝔟)⁻¹ = (N𝔟)^{e₂}·(N𝔟)^{−1/d} ≤
N^{−1/d}·(N𝔟)^{e₂}`; summing and using `hEuler` gives `T_M − T_N ≤ N^{−1/d}·E₂` for all `M`. -/
private theorem ciSup_sum_inv_absNorm_sub_le
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] {d : ℕ} {e₂ E₂ : ℝ} (he₂ : e₂ = (d : ℝ)⁻¹ - 1)
    (hE₂nn : 0 ≤ E₂)
    (hEuler : ∀ M : ℕ, ∑ 𝔟 ∈ (badFinset K L m M),
        ((Ideal.absNorm 𝔟 : ℝ)) ^ e₂ ≤ E₂)
    (N : ℕ) (hN1 : 1 ≤ N) :
    (⨆ M : ℕ, ∑ 𝔟 ∈ (badFinset K L m M), ((Ideal.absNorm 𝔟 : ℝ))⁻¹)
        - ∑ 𝔟 ∈ (badFinset K L m N), ((Ideal.absNorm 𝔟 : ℝ))⁻¹
      ≤ (N : ℝ) ^ (-(d : ℝ)⁻¹) * E₂ := by
  set Tfun : ℕ → ℝ :=
    fun N ↦ ∑ 𝔟 ∈ (badFinset K L m N), ((Ideal.absNorm 𝔟 : ℝ))⁻¹ with hTfun
  have hTmono : Monotone Tfun := fun N M hNM ↦
    Finset.sum_le_sum_of_subset_of_nonneg ((show ∀ {N M : ℕ} (hNM : N ≤ M), ((badFinset K L m N) ⊆ (badFinset K L m M)) from by
      intro N M hNM
      classical
      intro 𝔟 h
      rw [badFinset, Set.Finite.mem_toFinset] at h ⊢
      exact ⟨h.1, h.2.1, h.2.2.trans hNM⟩) hNM)
      (fun 𝔟 _ _ ↦ by positivity)
  have hNrpow_nn : (0 : ℝ) ≤ (N : ℝ) ^ (-(d : ℝ)⁻¹) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rw [sub_le_iff_le_add]
  refine ciSup_le fun M ↦ ?_
  rcases le_or_gt N M with hNM | hMN
  · have hsub : (badFinset K L m N) ⊆ (badFinset K L m M) :=
      (show ∀ {N M : ℕ} (hNM : N ≤ M), ((badFinset K L m N) ⊆ (badFinset K L m M)) from by
        intro N M hNM
        classical
        intro 𝔟 h
        rw [badFinset, Set.Finite.mem_toFinset] at h ⊢
        exact ⟨h.1, h.2.1, h.2.2.trans hNM⟩) hNM
    have hdiff : Tfun M - Tfun N
        = ∑ 𝔟 ∈ (badFinset K L m M) \ (badFinset K L m N),
            ((Ideal.absNorm 𝔟 : ℝ))⁻¹ := by
      simp only [hTfun]
      rw [sub_eq_iff_eq_add', ← Finset.sum_sdiff hsub, add_comm]
    have hperb : ∑ 𝔟 ∈ (badFinset K L m M) \ (badFinset K L m N),
          ((Ideal.absNorm 𝔟 : ℝ))⁻¹
        ≤ (N : ℝ) ^ (-(d : ℝ)⁻¹) *
          ∑ 𝔟 ∈ (badFinset K L m M), ((Ideal.absNorm 𝔟 : ℝ)) ^ e₂ := by
      rw [Finset.mul_sum]
      refine le_trans (Finset.sum_le_sum (fun 𝔟 h𝔟 ↦ ?_))
        (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          (fun 𝔟 _ _ ↦ mul_nonneg hNrpow_nn (Real.rpow_nonneg (by positivity) _)))
      simp only [Finset.mem_sdiff, badFinset, Set.Finite.mem_toFinset] at h𝔟
      obtain ⟨hin, hnotin⟩ := h𝔟
      have hb0 : Ideal.absNorm 𝔟 ≠ 0 := fun h ↦ hin.1 (Ideal.absNorm_eq_zero_iff.mp h)
      have hNb : N < Ideal.absNorm 𝔟 := by
        by_contra h; push Not at h; exact hnotin ⟨hin.1, hin.2.1, h⟩
      have hbposR : (0 : ℝ) < (Ideal.absNorm 𝔟 : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hb0
      have hNbR : (N : ℝ) ≤ (Ideal.absNorm 𝔟 : ℝ) := by exact_mod_cast hNb.le
      have hsplit : (Ideal.absNorm 𝔟 : ℝ)⁻¹
          = (Ideal.absNorm 𝔟 : ℝ) ^ e₂ * (Ideal.absNorm 𝔟 : ℝ) ^ (-(d : ℝ)⁻¹) := by
        rw [← Real.rpow_add hbposR, he₂,
          (by ring : ((d : ℝ)⁻¹ - 1) + (-(d : ℝ)⁻¹) = -1), Real.rpow_neg_one]
      rw [hsplit, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hN1) hNbR (neg_nonpos.mpr (by positivity)))
        (le_of_lt (Real.rpow_pos_of_pos hbposR _))
    have : Tfun M - Tfun N ≤ (N : ℝ) ^ (-(d : ℝ)⁻¹) * E₂ :=
      hdiff ▸ le_trans hperb (mul_le_mul_of_nonneg_left (hEuler M) hNrpow_nn)
    linarith
  · have : Tfun M ≤ Tfun N := hTmono hMN.le
    nlinarith [mul_nonneg hNrpow_nn hE₂nn]

/-! ### The final error assembly

With the `g`-uniform per-residue constants `(κ₀, C₀)` from the ICC count and the uniform
bad-part Euler bounds (`sum_rpow_badFinset_le`), the L2 fibre count
`count_g(N) = ∑_{𝔟 ∈ badFinset N} RC(autToPow(g·Frob𝔟⁻¹), ⌊N/N𝔟⌋)` (`card_L2_eq_sum_residue`) is
estimated by a triangle inequality into three pieces, each `O(N^{1−1/d})`:
* the per-bad-part effective errors `∑_𝔟 |RC − κ₀·⌊N/N𝔟⌋|`, bounded via `(κ₀, C₀)`;
* the floor-rounding slack `κ₀·∑_𝔟 (⌊N/N𝔟⌋ − N/N𝔟)`, each term in `[−1,0]`;
* the bad-part tail `κ₀·N·(T − T_N)`, where `T = ⨆_N ∑_{𝔟 ∈ badFinset N} (N𝔟)⁻¹` and the tail
  `T − T_N ≤ N^{−1/d}·E₂` is read off the Euler bound at exponent `1/d − 1` on the difference set.
The leading constant is `κ = κ₀·T`, `g`-independent. This needs `d ≥ 2` so that `1/d − 1 < 0` and
the Euler products converge; the `d = 1` (`K = ℚ`) case has an **empty** bad-prime set
(`badFinset N = {⊤}`) and is handled separately. -/

open UniqueFactorizationMonoid nonZeroDivisors in
/-- **The L2 fibre bound, `d ≥ 2` branch.** The bad-part Euler tail converges. -/
private theorem card_fibre_bound_two_le {ζ : L} (hζ : IsPrimitiveRoot ζ m)
    (hd : 2 ≤ Module.finrank ℚ K) :
    ∃ κ C' : ℝ, ∀ g : Gal(L/K), ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
            (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ frobeniusIdeal K L 𝔞 = g} : ℝ)
          - κ * (N : ℝ)|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  set d : ℕ := Module.finrank ℚ K
  set α : ℝ := 1 - (d : ℝ)⁻¹ with hα
  set e₂ : ℝ := (d : ℝ)⁻¹ - 1 with he₂
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by lia)
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have he₂neg : e₂ < 0 := by
    have hle : (d : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by gcongr
    rw [he₂]; linarith [hle, (by norm_num : (2 : ℝ)⁻¹ < 1)]
  have hαnn : 0 ≤ α := by rw [hα]; linarith [he₂neg, he₂]
  have hαe₂ : α = -e₂ := by rw [hα, he₂]; ring
  have hbad : {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ (Ideal.absNorm 𝔭).Coprime m}.Finite := by
    classical
    refine Set.Finite.subset
      (Set.Finite.biUnion (s := (↑m.primeFactors : Set ℕ))
        (t := fun p : ℕ =>
          {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ (p : 𝓞 K) ∈ 𝔭})
        (Set.toFinite _) fun p hp ↦ ?_)
      ?_
    · have hp0 : p ≠ 0 := (Nat.pos_of_mem_primeFactors hp).ne'
      have hspan : (Ideal.span {(p : 𝓞 K)}) ≠ 0 := by
        simp only [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
        exact_mod_cast hp0
      refine ((Ideal.finite_factors (R := 𝓞 K) hspan).image (·.asIdeal)).subset ?_
      rintro 𝔭 ⟨hprime, hne, hmem⟩
      exact ⟨⟨𝔭, hprime, hne⟩,
        Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem), rfl⟩
    · rintro 𝔭 ⟨hprime, hne, hncop⟩
      have := hprime
      have hfactor : ∃ p ∈ m.primeFactors, (p : 𝓞 K) ∈ 𝔭 := by
        have h𝔭 : 𝔭 ≠ ⊥ := hne
        have hN0 : Ideal.absNorm 𝔭 ≠ 0 :=
          fun h ↦ h𝔭 (Ideal.absNorm_eq_zero_iff.mp h)
        have hN1' : Ideal.absNorm 𝔭 ≠ 1 :=
          fun h ↦ ‹𝔭.IsPrime›.ne_top (Ideal.absNorm_eq_one_iff.mp h)
        obtain ⟨r, hr, hrdvd, hrm⟩ :=
          exists_prime_dvd_natCast_mem K 𝔭 _ (by lia) (Ideal.absNorm_mem 𝔭)
        have hNdvd : Ideal.absNorm 𝔭 ∣ r ^ Module.finrank ℤ (𝓞 K) := by
          have hd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hrm)
          rw [Ideal.absNorm_span_singleton,
            show ((r : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (r : ℤ) by
              push_cast
              rfl,
            Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at hd
          exact hd
        obtain ⟨p, hp, hpdvd⟩ :=
          Nat.exists_prime_and_dvd (hncop : Nat.gcd (Ideal.absNorm 𝔭) m ≠ 1)
        have hpr : p ∣ r ^ Module.finrank ℤ (𝓞 K) :=
          (hpdvd.trans (Nat.gcd_dvd_left _ _)).trans hNdvd
        have hpeqr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpr)
        exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans (Nat.gcd_dvd_right _ _), NeZero.ne m⟩,
          hpeqr ▸ hrm⟩
      obtain ⟨p, hp, hpmem⟩ := hfactor
      exact Set.mem_biUnion hp ⟨hprime, hne, hpmem⟩
  set P : Finset (Ideal (𝓞 K)) := hbad.toFinset with hP
  have hN𝔭2 : ∀ 𝔭 ∈ P, (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ) := by
    intro 𝔭 h𝔭
    rw [hP, Set.Finite.mem_toFinset] at h𝔭
    have h1 : Ideal.absNorm 𝔭 ≠ 1 := fun h ↦ h𝔭.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    have h0 : Ideal.absNorm 𝔭 ≠ 0 := fun h ↦ h𝔭.2.1 (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast (show 2 ≤ Ideal.absNorm 𝔭 by lia)
  have hxlt : ∀ e : ℝ, e < 0 → ∀ 𝔭 ∈ P, ((Ideal.absNorm 𝔭 : ℝ)) ^ e < 1 := by
    intro e he 𝔭 h𝔭
    exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith [hN𝔭2 𝔭 h𝔭]) he
  have hxlt1 : ∀ 𝔭 ∈ P, ((Ideal.absNorm 𝔭 : ℝ)) ^ (-1 : ℝ) < 1 := hxlt _ (by norm_num)
  have hxlt2 : ∀ 𝔭 ∈ P, ((Ideal.absNorm 𝔭 : ℝ)) ^ e₂ < 1 := hxlt _ he₂neg
  set E₁ : ℝ := ∏ 𝔭 ∈ P, (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ (-1 : ℝ))⁻¹
  set E₂ : ℝ := ∏ 𝔭 ∈ P, (1 - ((Ideal.absNorm 𝔭 : ℝ)) ^ e₂)⁻¹ with hE₂
  obtain ⟨κ₀, C₀, hunif⟩ :=
    exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform K m (hζ.autToPow K).range
      (fun χ hχ ↦ tendsto_sum_char_mul_cardNormLeResidue_div_of_realized K m
        (hζ.autToPow K).range
        (fun _ ha ↦ autToPow_range_le_realizedResidues K L m hζ ha) χ hχ)
  set Tfun : ℕ → ℝ :=
    fun N ↦ ∑ 𝔟 ∈ (badFinset K L m N), ((Ideal.absNorm 𝔟 : ℝ))⁻¹ with hTfun
  have hTfun_eq : ∀ N, Tfun N
      = ∑ 𝔟 ∈ (badFinset K L m N), ((Ideal.absNorm 𝔟 : ℝ)) ^ (-1 : ℝ) := by
    intro N
    rw [hTfun]; refine Finset.sum_congr rfl fun 𝔟 _ ↦ ?_
    rw [Real.rpow_neg_one]
  have hTbdd : ∀ N, Tfun N ≤ E₁ := fun N ↦ by
    rw [hTfun_eq N]; exact sum_rpow_badFinset_le K L m hbad N (-1) hxlt1
  have hTmono : Monotone Tfun := by
    intro N M hNM
    exact Finset.sum_le_sum_of_subset_of_nonneg ((show ∀ {N M : ℕ} (hNM : N ≤ M), ((badFinset K L m N) ⊆ (badFinset K L m M)) from by
      intro N M hNM
      classical
      intro 𝔟 h
      rw [badFinset, Set.Finite.mem_toFinset] at h ⊢
      exact ⟨h.1, h.2.1, h.2.2.trans hNM⟩) hNM)
      (fun 𝔟 _ _ ↦ by positivity)
  set T : ℝ := ⨆ N, Tfun N
  have hTbddAbove : BddAbove (Set.range Tfun) := ⟨E₁, fun y ⟨N, hN⟩ ↦ hN ▸ hTbdd N⟩
  have hTfun_le_T : ∀ N, Tfun N ≤ T := fun N ↦ le_ciSup hTbddAbove N
  have hE₂nn : 0 ≤ E₂ := by
    rw [hE₂]; refine Finset.prod_nonneg fun 𝔭 h𝔭 ↦ ?_
    have := hxlt2 𝔭 h𝔭; positivity
  have htail : ∀ N : ℕ, 1 ≤ N → T - Tfun N ≤ (N : ℝ) ^ (-(d : ℝ)⁻¹) * E₂ := fun N hN1 ↦
    ciSup_sum_inv_absNorm_sub_le K L m he₂ hE₂nn
      (fun M ↦ sum_rpow_badFinset_le K L m hbad M e₂ hxlt2) N hN1
  refine ⟨κ₀ * T, (C₀ + 2 * |κ₀|) * E₂, fun g N hN1 ↦ ?_⟩
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hNα_nn : (0 : ℝ) ≤ (N : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rw [card_L2_eq_sum_residue K L m hζ g N, Nat.cast_sum]
  set a : Ideal (𝓞 K) → (ZMod m)ˣ :=
    fun 𝔟 ↦ hζ.autToPow K (g * (frobeniusIdeal K L 𝔟)⁻¹)
  set RC : Ideal (𝓞 K) → ℝ := fun 𝔟 ↦
    (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N / Ideal.absNorm 𝔟 ∧
      ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m)) = ((a 𝔟 : (ZMod m)ˣ) : ZMod m)} : ℝ)
  change |(∑ 𝔟 ∈ (badFinset K L m N), RC 𝔟) - κ₀ * T * (N : ℝ)| ≤ _
  have hamem : ∀ 𝔟, a 𝔟 ∈ (hζ.autToPow K).range := fun 𝔟 ↦ ⟨_, rfl⟩
  have hC₀nn : 0 ≤ C₀ := by
    have h := hunif 1 (one_mem _) 1 (le_refl 1)
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at h
    exact le_trans (abs_nonneg _) h
  have hbadmem : ∀ 𝔟 ∈ (badFinset K L m N),
      𝔟 ≠ ⊥ ∧ Ideal.absNorm 𝔟 ≤ N := fun 𝔟 h𝔟 ↦ by
    rw [badFinset, Set.Finite.mem_toFinset] at h𝔟; exact ⟨h𝔟.1, h𝔟.2.2⟩
  have hperbad : ∀ 𝔟 ∈ (badFinset K L m N),
      |RC 𝔟 - κ₀ * ((N : ℝ) / (Ideal.absNorm 𝔟 : ℝ))|
        ≤ C₀ * (N : ℝ) ^ α * (Ideal.absNorm 𝔟 : ℝ) ^ e₂ + |κ₀| := by
    intro 𝔟 h𝔟
    obtain ⟨hb0, hbN⟩ := hbadmem 𝔟 h𝔟
    have hbpos : 0 < Ideal.absNorm 𝔟 :=
      Nat.pos_of_ne_zero fun h ↦ hb0 (Ideal.absNorm_eq_zero_iff.mp h)
    exact (show ∀ {N Nb : ℕ} {RCb κ₀ C₀ α e₂ : ℝ} (hNb : 0 < Nb)
    (hαnn : 0 ≤ α) (hαe₂ : α = -e₂) (hC₀nn : 0 ≤ C₀)
    (heff : |RCb - κ₀ * ((N / Nb : ℕ) : ℝ)| ≤ C₀ * ((N / Nb : ℕ) : ℝ) ^ α),
      |RCb - κ₀ * ((N : ℝ) / (Nb : ℝ))| ≤ C₀ * (N : ℝ) ^ α * (Nb : ℝ) ^ e₂ + |κ₀| from by
      intro N Nb RCb κ₀ C₀ α e₂ hNb hαnn hαe₂ hC₀nn heff
      have hbposR : (0 : ℝ) < (Nb : ℝ) := by exact_mod_cast hNb
      have hWle : ((N / Nb : ℕ) : ℝ) ≤ (N : ℝ) / (Nb : ℝ) := by
        rw [le_div_iff₀ hbposR]; exact_mod_cast Nat.div_mul_le_self N Nb
      have hWslack : (N : ℝ) / (Nb : ℝ) - ((N / Nb : ℕ) : ℝ) ≤ 1 := by
        rw [sub_le_iff_le_add, div_le_iff₀ hbposR]
        have hlt : N < (N / Nb + 1) * Nb := by
          have hm := Nat.mod_lt N hNb; have hdm := Nat.div_add_mod N Nb
          rw [add_mul, one_mul, mul_comm]; omega
        have : (N : ℝ) < ((N / Nb : ℕ) + 1) * (Nb : ℝ) := by exact_mod_cast hlt
        nlinarith [this]
      have hpow_le : ((N / Nb : ℕ) : ℝ) ^ α ≤ (N : ℝ) ^ α * (Nb : ℝ) ^ e₂ := by
        have heq : (N : ℝ) ^ α * (Nb : ℝ) ^ e₂ = ((N : ℝ) / (Nb : ℝ)) ^ α := by
          rw [Real.div_rpow (Nat.cast_nonneg N) hbposR.le, div_eq_mul_inv]
          congr 1
          rw [hαe₂, Real.rpow_neg hbposR.le, inv_inv]
        rw [heq]
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) hWle hαnn
      calc |RCb - κ₀ * ((N : ℝ) / (Nb : ℝ))|
          ≤ |RCb - κ₀ * ((N / Nb : ℕ) : ℝ)|
            + |κ₀ * ((N / Nb : ℕ) : ℝ) - κ₀ * ((N : ℝ) / (Nb : ℝ))| := by
            simpa using abs_add_le (RCb - κ₀ * ((N / Nb : ℕ) : ℝ))
              (κ₀ * ((N / Nb : ℕ) : ℝ) - κ₀ * ((N : ℝ) / (Nb : ℝ)))
        _ ≤ C₀ * ((N / Nb : ℕ) : ℝ) ^ α + |κ₀| * 1 := by
            gcongr
            rw [← mul_sub, abs_mul]
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            rw [abs_le]
            constructor <;> [linarith [hWle]; linarith [hWslack]]
        _ ≤ C₀ * ((N : ℝ) ^ α * (Nb : ℝ) ^ e₂) + |κ₀| := by rw [mul_one]; gcongr
        _ = C₀ * (N : ℝ) ^ α * (Nb : ℝ) ^ e₂ + |κ₀| := by ring) hbpos hαnn hαe₂ hC₀nn
      (hunif (a 𝔟) (hamem 𝔟) _ ((Nat.one_le_div_iff hbpos).mpr hbN))
  have hsum_div : ∑ 𝔟 ∈ (badFinset K L m N), (N : ℝ) / (Ideal.absNorm 𝔟 : ℝ)
      = (N : ℝ) * Tfun N := by
    rw [hTfun, Finset.mul_sum]
    refine Finset.sum_congr rfl fun 𝔟 _ ↦ ?_
    rw [div_eq_mul_inv]
  have hsumE₂ : ∑ 𝔟 ∈ (badFinset K L m N), ((Ideal.absNorm 𝔟 : ℝ)) ^ e₂ ≤ E₂ :=
    sum_rpow_badFinset_le K L m hbad N e₂ hxlt2
  have hcard_le : (((badFinset K L m N).card : ℕ) : ℝ) ≤ (N : ℝ) ^ α * E₂ := by
    calc (((badFinset K L m N).card : ℕ) : ℝ)
        = ∑ _𝔟 ∈ (badFinset K L m N), (1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ 𝔟 ∈ (badFinset K L m N), (N : ℝ) ^ α * (Ideal.absNorm 𝔟 : ℝ) ^ e₂ := by
          refine Finset.sum_le_sum fun 𝔟 h𝔟 ↦ ?_
          rw [badFinset, Set.Finite.mem_toFinset] at h𝔟
          have hbpos : 0 < Ideal.absNorm 𝔟 :=
            Nat.pos_of_ne_zero fun h ↦ h𝔟.1 (Ideal.absNorm_eq_zero_iff.mp h)
          have hbposR : (0 : ℝ) < (Ideal.absNorm 𝔟 : ℝ) := by exact_mod_cast hbpos
          have hbNR : (Ideal.absNorm 𝔟 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h𝔟.2.2
          have h1eq : (1 : ℝ) = (Ideal.absNorm 𝔟 : ℝ) ^ α * (Ideal.absNorm 𝔟 : ℝ) ^ e₂ := by
            rw [← Real.rpow_add hbposR, hαe₂, neg_add_cancel, Real.rpow_zero]
          rw [h1eq]
          exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hbposR.le hbNR hαnn)
            (Real.rpow_pos_of_pos hbposR _).le
      _ = (N : ℝ) ^ α * ∑ 𝔟 ∈ (badFinset K L m N),
            (Ideal.absNorm 𝔟 : ℝ) ^ e₂ := by rw [Finset.mul_sum]
      _ ≤ (N : ℝ) ^ α * E₂ := mul_le_mul_of_nonneg_left hsumE₂ hNα_nn
  have hA : |∑ 𝔟 ∈ (badFinset K L m N),
        (RC 𝔟 - κ₀ * ((N : ℝ) / (Ideal.absNorm 𝔟 : ℝ)))|
      ≤ (C₀ + |κ₀|) * ((N : ℝ) ^ α * E₂) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ 𝔟 ∈ (badFinset K L m N),
          |RC 𝔟 - κ₀ * ((N : ℝ) / (Ideal.absNorm 𝔟 : ℝ))|
        ≤ ∑ 𝔟 ∈ (badFinset K L m N),
            (C₀ * (N : ℝ) ^ α * (Ideal.absNorm 𝔟 : ℝ) ^ e₂ + |κ₀|) :=
          Finset.sum_le_sum hperbad
      _ = C₀ * (N : ℝ) ^ α * (∑ 𝔟 ∈ (badFinset K L m N),
            (Ideal.absNorm 𝔟 : ℝ) ^ e₂)
          + |κ₀| * (((badFinset K L m N).card : ℕ) : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ C₀ * (N : ℝ) ^ α * E₂ + |κ₀| * ((N : ℝ) ^ α * E₂) := by
          refine add_le_add (mul_le_mul_of_nonneg_left hsumE₂ (mul_nonneg hC₀nn hNα_nn))
            (mul_le_mul_of_nonneg_left hcard_le (abs_nonneg _))
      _ = (C₀ + |κ₀|) * ((N : ℝ) ^ α * E₂) := by ring
  have hB : |κ₀ * ((∑ 𝔟 ∈ (badFinset K L m N),
        (N : ℝ) / (Ideal.absNorm 𝔟 : ℝ)) - T * (N : ℝ))|
      ≤ |κ₀| * ((N : ℝ) ^ α * E₂) := by
    rw [hsum_div, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hTrw : (N : ℝ) * Tfun N - T * (N : ℝ) = -((N : ℝ) * (T - Tfun N)) := by ring
    rw [hTrw, abs_neg, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg N)
      (sub_nonneg.mpr (hTfun_le_T N)))]
    refine le_trans (mul_le_mul_of_nonneg_left (htail N hN1) (Nat.cast_nonneg N)) ?_
    rw [← mul_assoc, hα]
    have hNmul : (N : ℝ) * (N : ℝ) ^ (-(d : ℝ)⁻¹) = (N : ℝ) ^ (1 - (d : ℝ)⁻¹) := by
      nth_rewrite 1 [← Real.rpow_one (N : ℝ)]
      rw [← Real.rpow_add hNposR, sub_eq_add_neg]
    rw [hNmul]
  have hdecomp : (∑ 𝔟 ∈ (badFinset K L m N), RC 𝔟) - κ₀ * T * (N : ℝ)
      = (∑ 𝔟 ∈ (badFinset K L m N),
          (RC 𝔟 - κ₀ * ((N : ℝ) / (Ideal.absNorm 𝔟 : ℝ))))
        + κ₀ * ((∑ 𝔟 ∈ (badFinset K L m N),
          (N : ℝ) / (Ideal.absNorm 𝔟 : ℝ)) - T * (N : ℝ)) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; ring
  rw [hdecomp]
  refine le_trans (abs_add_le _ _) ?_
  have hgoal : (C₀ + 2 * |κ₀|) * E₂ * (N : ℝ) ^ α
      = (C₀ + |κ₀|) * ((N : ℝ) ^ α * E₂) + |κ₀| * ((N : ℝ) ^ α * E₂) := by ring
  rw [hgoal]
  exact add_le_add hA hB

/-! ### Sub-lemmas for `coprime_absNorm_of_unramified_of_finrank_eq_one` (the `d = 1` branch)

The `d = 1` ramification fact is discharged **K-internally** (no `K ≃ ℚ` transport) via the
different ideal: a rational prime `p ∣ m` (with `m % 4 ≠ 2`) extracted from a non-coprime norm
gives a primitive `p^v`-th root `ζ'` in `𝓞 L`; the Eisenstein identity
`(p) = (ζ' − 1)^{φ(p^v)}` (with `φ(p^v) ≥ 2`) forces `𝔓² ∣ (𝔭)·𝓞 L` for any `𝔓` over `𝔭`,
hence `𝔓 ∣ differentIdeal (𝓞 K) (𝓞 L)`
(`pow_sub_one_dvd_differentIdeal`), contradicting unramifiedness. -/

omit [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] in
/-- At `[K : ℚ] = 1`, an unramified prime ideal has norm coprime to `m` when `m % 4 ≠ 2`.
A prime `p ∣ m` extracted from a non-coprime norm belongs to `𝔭`. A primitive `p^v`-th root
in `𝓞 L` gives the Eisenstein associatedness identity with exponent `φ(p^v) ≥ 2`.
Since `(p) = 𝔭` in degree one, this forces a prime above `𝔭` to divide the different ideal,
contradicting unramifiedness through `not_dvd_differentIdeal_iff`. -/
private theorem coprime_absNorm_of_unramified_of_finrank_eq_one
    (hd1 : Module.finrank ℚ K = 1) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥)
    (hunr : UnramifiedIn K L 𝔭) (hm : m % 4 ≠ 2) : (Ideal.absNorm 𝔭).Coprime m := by
  classical
  by_contra hncop
  have hfactor : ∃ p ∈ m.primeFactors, (p : 𝓞 K) ∈ 𝔭 := by
    have hN0 : Ideal.absNorm 𝔭 ≠ 0 :=
      fun h ↦ h𝔭 (Ideal.absNorm_eq_zero_iff.mp h)
    have hN1' : Ideal.absNorm 𝔭 ≠ 1 :=
      fun h ↦ ‹𝔭.IsPrime›.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    obtain ⟨r, hr, hrdvd, hrm⟩ :=
      exists_prime_dvd_natCast_mem K 𝔭 _ (by lia) (Ideal.absNorm_mem 𝔭)
    have hNdvd : Ideal.absNorm 𝔭 ∣ r ^ Module.finrank ℤ (𝓞 K) := by
      have hd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hrm)
      rw [Ideal.absNorm_span_singleton,
        show ((r : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (r : ℤ) by
          push_cast
          rfl,
        Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at hd
      exact hd
    obtain ⟨p, hp, hpdvd⟩ :=
      Nat.exists_prime_and_dvd (hncop : Nat.gcd (Ideal.absNorm 𝔭) m ≠ 1)
    have hpr : p ∣ r ^ Module.finrank ℤ (𝓞 K) :=
      (hpdvd.trans (Nat.gcd_dvd_left _ _)).trans hNdvd
    have hpeqr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpr)
    exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans (Nat.gcd_dvd_right _ _), NeZero.ne m⟩,
      hpeqr ▸ hrm⟩
  obtain ⟨p, hpm, hpmem𝔭⟩ := hfactor
  have hp : p.Prime := (Nat.mem_primeFactors.mp hpm).1
  haveI : Fact p.Prime := ⟨hp⟩
  have hpdvd : p ∣ m := Nat.dvd_of_mem_primeFactors hpm
  have hm0 : m ≠ 0 := (Nat.mem_primeFactors.mp hpm).2.2
  set v := m.factorization p with hv
  have hv1 : 1 ≤ v := by rw [hv]; exact hp.factorization_pos_of_dvd hm0 hpdvd
  obtain ⟨k, hk⟩ : ∃ k, v = k + 1 := ⟨v - 1, by lia⟩
  have hbad : ¬ (p = 2 ∧ k = 0) := by
    rintro ⟨rfl, rfl⟩
    exact (show ∀ {m : ℕ} (hm0 : m ≠ 0) (hm : m % 4 ≠ 2), (m.factorization 2 ≠ 1) from by
      intro m hm0 hm
      classical
      intro hf
      have h2dvd : 2 ∣ m := by
        have h : (2 : ℕ) ^ 1 ∣ m :=
          (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm0).mpr (by lia)
        simpa using h
      have h4ndvd : ¬ 4 ∣ m := fun h4 ↦
        absurd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm0).mp
          (by rwa [show (4 : ℕ) = 2 ^ 2 by norm_num] at h4)) (by lia)
      exact hm (by omega)) hm0 hm (by rw [← hv, hk])
  have hpvdvd : p ^ v ∣ m := by rw [hv]; exact Nat.ordProj_dvd m p
  obtain ⟨ζm, hζm⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot K L (Set.mem_singleton m) (NeZero.ne m)
  set q := m / p ^ v with hq
  have hqdvd : q ∣ m := Nat.div_dvd_of_dvd hpvdvd
  have hq0 : q ≠ 0 := Nat.div_ne_zero_iff.mpr
    ⟨pow_ne_zero _ hp.ne_zero, Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hpvdvd⟩
  set ζ' : 𝓞 L := hζm.toInteger ^ q
  have hmq : m / q = p ^ (k + 1) := by rw [hq, Nat.div_div_self hpvdvd hm0, ← hk]
  have hζ' : IsPrimitiveRoot ζ' (p ^ (k + 1)) := by
    have h := hζm.toInteger_isPrimitiveRoot.pow_of_dvd hq0 hqdvd
    rwa [hmq] at h
  have hassoc : Associated (p : 𝓞 L) ((ζ' - 1) ^ (p ^ k * (p - 1))) :=
    (show ∀ {p k : ℕ} [hp : Fact p.Prime] {ζ' : (𝓞 L)} (hζ' : IsPrimitiveRoot ζ' (p ^ (k + 1))), (Associated (p : (𝓞 L)) ((ζ' - 1) ^ (p ^ k * (p - 1)))) from by
      intro p k hp ζ' hζ'
      classical
      have hcard : (primitiveRoots (p ^ (k + 1)) (𝓞 L)).card = p ^ k * (p - 1) := by
        rw [hζ'.card_primitiveRoots, Nat.totient_prime_pow_succ hp.out]
      have heval : (p : (𝓞 L)) = ∏ μ ∈ primitiveRoots (p ^ (k + 1)) (𝓞 L), (1 - μ) := by
        have h1 := eval_one_cyclotomic_prime_pow (R := (𝓞 L)) k (p := p)
        rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ'] at h1
        simp only [eval_prod, eval_sub, eval_X, eval_C] at h1
        rw [← h1]
      rw [heval]
      have hpos : 0 < p ^ (k + 1) := pow_pos hp.out.pos _
      have hassoc : ∀ μ ∈ primitiveRoots (p ^ (k + 1)) (𝓞 L), Associated (1 - μ) (ζ' - 1) := by
        intro μ hμ
        have hμp : IsPrimitiveRoot μ (p ^ (k + 1)) := isPrimitiveRoot_of_mem_primitiveRoots hμ
        obtain ⟨j, _, rfl⟩ := hζ'.eq_pow_of_pow_eq_one hμp.pow_eq_one
        have hjc : j.Coprime (p ^ (k + 1)) := (hζ'.pow_iff_coprime hpos j).mp hμp
        rw [show (1 : (𝓞 L)) - ζ' ^ j = -(ζ' ^ j - 1) by ring]
        exact (hζ'.associated_sub_one_pow_sub_one_of_coprime hjc).neg_right.symm
      calc Associated (∏ μ ∈ primitiveRoots (p ^ (k + 1)) (𝓞 L), (1 - μ))
            (∏ _μ ∈ primitiveRoots (p ^ (k + 1)) (𝓞 L), (ζ' - 1)) := Associated.prod _ _ _ hassoc
        _ = (ζ' - 1) ^ (p ^ k * (p - 1)) := by rw [Finset.prod_const, hcard]) hζ'
  have hφ2 : 2 ≤ p ^ k * (p - 1) := (show ∀ {p k : ℕ} (hp : p.Prime) (hbad : ¬ (p = 2 ∧ k = 0)), (2 ≤ p ^ k * (p - 1)) from by
    intro p k hp hbad
    classical
    rcases eq_or_ne p 2 with rfl | hp2
    · have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr fun h ↦ hbad ⟨rfl, h⟩
      calc 2 = 2 ^ 1 * (2 - 1) := by norm_num
        _ ≤ 2 ^ k * (2 - 1) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hk)
    · have hp3 : 3 ≤ p := hp.two_le.lt_of_ne (Ne.symm hp2)
      calc 2 ≤ 1 * (p - 1) := by lia
        _ ≤ p ^ k * (p - 1) := Nat.mul_le_mul_right _ (Nat.one_le_pow _ _ hp.pos)) hp hbad
  have hspan𝔭 : Ideal.span {(p : 𝓞 K)} = 𝔭 :=
    (show ∀ (hd1 : Module.finrank ℚ K = 1) (p : ℕ) (hp : p.Prime) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (hmem : (p : 𝓞 K) ∈ 𝔭),
      Ideal.span {(p : 𝓞 K)} = 𝔭 from by
      intro hd1 p hp 𝔭 instP hmem
      have hrank : Module.finrank ℤ (𝓞 K) = 1 := by rw [NumberField.RingOfIntegers.rank, hd1]
      have hNspan : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p := by
        rw [Ideal.absNorm_span_singleton,
          show ((p : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) by push_cast; rfl,
          Algebra.norm_algebraMap, hrank, Int.natAbs_pow, Int.natAbs_natCast, pow_one]
      have hle : Ideal.span {(p : 𝓞 K)} ≤ 𝔭 := (Ideal.span_singleton_le_iff_mem _).mpr hmem
      obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
      have hNmul : Ideal.absNorm 𝔭 * Ideal.absNorm C = p := by rw [← map_mul, ← hC, hNspan]
      have hN𝔭1 : Ideal.absNorm 𝔭 ≠ 1 := fun h ↦ ‹𝔭.IsPrime›.ne_top (Ideal.absNorm_eq_one_iff.mp h)
      have hN𝔭eq : Ideal.absNorm 𝔭 = p :=
        (Nat.Prime.eq_one_or_self_of_dvd hp _ ⟨_, hNmul.symm⟩).resolve_left hN𝔭1
      have hNC1 : Ideal.absNorm C = 1 := by
        rw [hN𝔭eq] at hNmul
        exact Nat.eq_of_mul_eq_mul_left hp.pos (by rwa [mul_one])
      rw [hC, Ideal.absNorm_eq_one_iff.mp hNC1, Ideal.mul_top]) hd1 p hp 𝔭 hpmem𝔭
  haveI : 𝔭.IsMaximal := ‹𝔭.IsPrime›.isMaximal h𝔭
  obtain ⟨𝔓, h𝔓max, h𝔓lo⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := 𝓞 K) (S := 𝓞 L) 𝔭
  haveI : 𝔓.IsPrime := h𝔓max.isPrime
  haveI := h𝔓lo
  have hnotdvd : ¬ 𝔓 ∣ differentIdeal (𝓞 K) (𝓞 L) := by
    rw [not_dvd_differentIdeal_iff (A := 𝓞 K) (B := 𝓞 L)]
    exact hunr.2 𝔓 h𝔓max h𝔓lo
  apply hnotdvd
  have hdvd2 : 𝔓 ^ 2 ∣ 𝔭.map (algebraMap (𝓞 K) (𝓞 L)) := by
    have hmapeq : 𝔭.map (algebraMap (𝓞 K) (𝓞 L)) = Ideal.span {(p : 𝓞 L)} := by
      rw [← hspan𝔭, Ideal.map_span, Set.image_singleton, map_natCast]
    have hspanL : Ideal.span {(p : 𝓞 L)} = (Ideal.span {ζ' - 1}) ^ (p ^ k * (p - 1)) := by
      rw [Ideal.span_singleton_pow]
      exact Ideal.span_singleton_eq_span_singleton.mpr hassoc
    have hpmem𝔓 : (p : 𝓞 L) ∈ 𝔓 := by
      have h1 : algebraMap (𝓞 K) (𝓞 L) (p : 𝓞 K) ∈ 𝔓 := by
        rw [h𝔓lo.over] at hpmem𝔭; exact hpmem𝔭
      rwa [map_natCast] at h1
    have hsub𝔓 : ζ' - 1 ∈ 𝔓 := by
      have hpow : (ζ' - 1) ^ (p ^ k * (p - 1)) ∈ 𝔓 := by
        obtain ⟨u, hu⟩ := hassoc
        rw [← hu]; exact Ideal.mul_mem_right _ _ hpmem𝔓
      exact ‹𝔓.IsPrime›.mem_of_pow_mem _ hpow
    have hdvd1 : 𝔓 ∣ Ideal.span {ζ' - 1} :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hsub𝔓)
    rw [hmapeq, hspanL]
    exact dvd_trans (pow_dvd_pow 𝔓 hφ2) (pow_dvd_pow_of_dvd hdvd1 _)
  simpa using pow_sub_one_dvd_differentIdeal (𝓞 K) 𝔓 2 h𝔭 hdvd2

/-- **The L2 fibre bound, `d = 1` branch.** When `[K : ℚ] = 1` the bad-prime set is empty, so the
bad-part set is the single ideal `⊤` (`badFinset N = {⊤}`) and the L2 count is one good-fibre count
`RC(autToPow g, N)`, bounded directly by the `g`-uniform ICC estimate with
`κ = κ₀`, `C' = C₀`. -/
private theorem card_fibre_bound_eq_one {ζ : L} (hζ : IsPrimitiveRoot ζ m)
    (hd1 : Module.finrank ℚ K = 1) (hm : m % 4 ≠ 2) :
    ∃ κ C' : ℝ, ∀ g : Gal(L/K), ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
            (∀ 𝔭 ∈ normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧ frobeniusIdeal K L 𝔞 = g} : ℝ)
          - κ * (N : ℝ)|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  obtain ⟨κ₀, C₀, hunif⟩ :=
    exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform K m (hζ.autToPow K).range
      (fun χ hχ ↦ tendsto_sum_char_mul_cardNormLeResidue_div_of_realized K m
        (hζ.autToPow K).range
        (fun _ ha ↦ autToPow_range_le_realizedResidues K L m hζ ha) χ hχ)
  refine ⟨κ₀, C₀, fun g N hN1 ↦ ?_⟩
  have hbadtop : (badFinset K L m N) = {⊤} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun 𝔟 h𝔟 ↦ ?_⟩
    · rw [badFinset, Set.Finite.mem_toFinset]
      refine ⟨by rw [Ne, ← Ideal.one_eq_top]; exact one_ne_zero, fun 𝔭 h𝔭 ↦ ?_, ?_⟩
      · rw [← Ideal.one_eq_top, normalizedFactors_one] at h𝔭
        exact absurd h𝔭 (Multiset.notMem_zero _)
      · rw [Ideal.absNorm_top]; exact hN1
    · rw [badFinset, Set.Finite.mem_toFinset] at h𝔟
      obtain ⟨h0, hfac, _⟩ := h𝔟
      by_contra htop
      have hfac0 : normalizedFactors 𝔟 ≠ 0 := by
        intro h
        have : 𝔟 = 1 := by
          have hp := Ideal.prod_normalizedFactors_eq_self h0
          rw [h, Multiset.prod_zero] at hp; exact hp.symm
        rw [Ideal.one_eq_top] at this; exact htop this
      obtain ⟨𝔭, h𝔭⟩ := Multiset.exists_mem_of_ne_zero hfac0
      have hprime := prime_of_normalized_factor 𝔭 h𝔭
      haveI : 𝔭.IsPrime := Ideal.isPrime_of_prime hprime
      exact (hfac 𝔭 h𝔭).2 (coprime_absNorm_of_unramified_of_finrank_eq_one K L m hd1 𝔭
        hprime.ne_zero (hfac 𝔭 h𝔭).1 hm)
  rw [card_L2_eq_sum_residue K L m hζ g N, hbadtop, Finset.sum_singleton,
    (show ∀      
        [IsMulCommutative Gal(L/K)], frobeniusIdeal K L ⊤ = 1 from by
      intro attributeInstance0
      letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
      rw [frobeniusIdeal, ← Ideal.one_eq_top, UniqueFactorizationMonoid.normalizedFactors_one,
        Multiset.map_zero, Multiset.prod_zero]), inv_one, mul_one, Ideal.absNorm_top, Nat.div_one]
  exact hunif (hζ.autToPow K g) ⟨g, rfl⟩ N hN1

end L2Assembly

/-- **L2 — unramified-supported Frobenius-fibre equidistribution.** For
`L = K(μ_m)` cyclotomic, the number of nonzero ideals `𝔞` with `N𝔞 ≤ N`, **every prime factor of
`𝔞` unramified in `L`** (`U 𝔞`) and `Frob_𝔞 = g` is `κ·N + O(N^{1−1/d})` with the leading constant
`κ` **independent of `g`** (`d = finrank ℚ K`).

`U 𝔞` is the exact support condition (`galoisCharacterOnIdeal χ 𝔞 ≠ 0`). The geometry-of-numbers
argument splits an unramified-supported `𝔞` multiplicatively into its **"bad-prime" part** — the
product of factors that are unramified but have `N𝔭` *not* coprime to `m` (so `𝔭 ∣ m`; these are
the finitely many primes lying over the `p ∣ m` for which `K_𝔭` already contains `μ_{p^{v_p(m)}}`,
hence unramified despite ramifying naively over `ℚ`), whose ideal Frobenius is **not** the
norm-power — times a **"good" part** with `N𝔭` coprime to `m`, on which
native root-of-unity Frobenius formula gives `Frob_𝔭 = (Frob_p)^{f_𝔭}` cut out by `N𝔭 mod m`.

The bad-prime part ranges over a **fixed finite set** of ideals (products of the finitely many
bad primes); the partition `card_L2_eq_sum_residue` rewrites the L2 count as a
sum over the finite bad-part set `badFinset N` of **good-fibre norm-residue counts** at the residue
`autToPow (g · Frob𝔟⁻¹) ∈ range autToPow`, each over the window `⌊N/N𝔟⌋`. The κ-uniform
per-residue ICC count (one `(κ₀, C₀)` for every residue in `range autToPow`, the
`g`-independence input) comes from the ICC count `exists_card_norm_le_norm_residue_..._uniform` fed
its Fourier-decay hypothesis by the ICC producer + the realized-residue inclusion
(every cyclotomic-character value is an ideal-norm residue, via the coprime-restricted
Frobenii-generation `subgroup_eq_top_of_forall_frobenius_mem_of_coprime`). A triangle inequality
sums the per-bad-part errors and the bad-part Euler tail (`sum_rpow_le_euler_prod`, convergent for
`d ≥ 2`) into the effective `O(N^{1−1/d})` rate with `κ = κ₀·∑_{𝔟 bad}(N𝔟)⁻¹` `g`-independent; the
`d = 1` (`K = ℚ`) case has an empty bad set, so the count is one good-fibre residue count.

The `d = 1` "bad primes are empty" fact `coprime_absNorm_of_unramified_of_finrank_eq_one` is
discharged K-internally via the cyclotomic Eisenstein identity (no `K ≃ ℚ` transport); the whole
assembly is `sorry`-free. -/
theorem exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K L] (hm : m % 4 ≠ 2) :
    ∃ κ C' : ℝ, ∀ g : Gal(L/K), ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {𝔞 : Ideal (𝓞 K) //
            𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ N ∧
              (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞, UnramifiedIn K L 𝔭) ∧
                frobeniusIdeal K L 𝔞 = g} : ℝ)
          - κ * (N : ℝ)|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot K L (Set.mem_singleton m) (NeZero.ne m)
  rcases Nat.lt_or_ge (Module.finrank ℚ K) 2 with hlt | hge
  · have hd1 : Module.finrank ℚ K = 1 := le_antisymm (by lia) Module.finrank_pos
    exact card_fibre_bound_eq_one K L m hζ hd1 hm
  · exact card_fibre_bound_two_le K L m hζ hge

end Chebotarev
