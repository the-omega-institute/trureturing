/- GID: D5/S3/Factorization/Galois/GoldenCubicCompatibilityPrimeTransfer
   generality: I
   mirror-B: D5/B/S3/Factorization/Galois/GoldenCubicCompatibilityPrimeTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual rational-prime Frobenius event is exactly the unramified Chebotarev class event after removing finitely many primes. -/
import D5.S3.Factorization.Galois.GoldenCubicCompatibilityConjugacy
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Polynomial NumberField
open Filter Set Topology Chebotarev
open scoped Pointwise nonZeroDivisors

open D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness
open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open D5.S3.Factorization.QuadraticIdeals.EisensteinCyclotomicBridge
open D5.S3.Factorization.QuadraticIdeals.CubicIdealCharacter
open scoped NumberField

def ActualPrimeTransferData (j : ℕ) (a : (ZMod (modulus j))ˣ) : Prop :=
    letI : IsCyclotomicExtension {3} ℚ E := CyclotomicField.isCyclotomicExtension 3 ℚ
    ∃ ζ : L, IsPrimitiveRoot ζ (modulus j) ∧
      ∃ π : ℕ → EisensteinOrder, ∃ root : radicalIndex j → L,
        let φ : EisensteinOrder ≃ₐ[ℤ] 𝓞 E :=
          Classical.choice eisenstein_cyclotomic_equiv_exists
        let B : ℕ → ℕ := blockValue
        let S : Finset ℕ := support j
        let I := radicalIndex j
        let f : EisensteinOrder →+* E :=
          (algebraMap (𝓞 E) E).comp φ.toRingHom
        let ξ : E := f QuadraticAlgebra.omega
        let lam : EisensteinOrder := 1 + 2 * QuadraticAlgebra.omega
        let κ : {p : ℕ // p ∈ S} → E := fun p =>
          f (localCubicSymbol (Ideal.span {π p.1}) lam)
        let target : I → E := Sum.elim
          (fun w => if w.2 then (κ w.1)⁻¹ ^ 2 else (κ w.1) ^ 2)
          (fun _ => ξ ^ 2)
        ((∀ p ∈ S,
          (Ideal.span {π p}).IsPrime ∧ QuadraticAlgebra.norm (π p) = (p : ℤ) ∧
          (3 : EisensteinOrder) ∣ π p - 1 ∧ p % 3 = 1 ∧
          IsCoprime (π p) (star (π p))) ∧
        (∀ p ∈ S, ∀ q ∈ S, p ≠ q →
          IsCoprime (π p) (π q) ∧ IsCoprime (π p) (star (π q)) ∧
          IsCoprime (star (π p)) (π q) ∧
          IsCoprime (star (π p)) (star (π q))) ∧
        (∀ i, 1 ≤ i → i < j →
          orientedFactor ((D5.S1.Scale.goldenLucas (3 ^ i) - 1).toNat) =
            ∏ p ∈ (B i).primeFactors,
              π p ^ padicValNat p
                (Nat.fib (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p))) ∧
        (∀ v : I, root v ^ 3 = algebraMap E L
          ((Sum.elim (fun w => φ (if w.2 then star (π w.1.val) else π w.1.val))
            (fun k => if k.val = 0 then (2 : 𝓞 E) else 3) v) : E)) ∧
        Module.finrank E (IntermediateField.adjoin E (Set.range root)) =
          3 ^ (2 * S.card + 2) ∧
        (∀ x : IntermediateField.adjoin E (Set.range root),
          x ^ 3 ≠ algebraMap E (IntermediateField.adjoin E (Set.range root))
            (IsCyclotomicExtension.zeta 3 ℚ E)) ∧
        IsGalois E (IntermediateField.adjoin E (Set.range root)) ∧
        (∃ e : ((IntermediateField.adjoin E (Set.range root)) ≃ₐ[E]
            (IntermediateField.adjoin E (Set.range root))) ≃*
            (I → Multiplicative (ZMod 3)),
          ∀ σ : (IntermediateField.adjoin E (Set.range root)) ≃ₐ[E]
              (IntermediateField.adjoin E (Set.range root)), ∀ i : I,
            σ (⟨root i, IntermediateField.subset_adjoin E (Set.range root)
                ⟨i, rfl⟩⟩ : IntermediateField.adjoin E (Set.range root)) =
              algebraMap E (IntermediateField.adjoin E (Set.range root))
                (IsCyclotomicExtension.zeta 3 ℚ E) ^
                (Multiplicative.toAdd (e σ i)).val *
                  (⟨root i, IntermediateField.subset_adjoin E (Set.range root)
                    ⟨i, rfl⟩⟩ : IntermediateField.adjoin E (Set.range root)))) ∧
        (∀ p : {p : ℕ // p ∈ S},
          let P : Ideal EisensteinOrder := Ideal.span {π p.1}
          let q := Ideal.Quotient.mk P
          lam ∉ P ∧ (3 : EisensteinOrder) ∉ P ∧
            q (localCubicSymbol P lam) = q lam ^ ((p.1 - 1) / 3)) ∧
        let M : IntermediateField E L := IntermediateField.adjoin E (Set.range root)
        let C : IntermediateField E L := actualCyclotomic ζ
        let F : IntermediateField E L := M ⊔ C
        M ⊓ C = ⊥ ∧
        let M' : IntermediateField E F :=
          IntermediateField.restrict (show M ≤ F from le_sup_left)
        let C' : IntermediateField E F :=
          IntermediateField.restrict (show C ≤ F from le_sup_right)
        let aM : M ≃ₐ[E] M' :=
          IntermediateField.restrictAlgEquiv (show M ≤ F from le_sup_left)
        let aC : C ≃ₐ[E] C' :=
          IntermediateField.restrictAlgEquiv (show C ≤ F from le_sup_right)
        let β : radicalIndex j → M := fun v =>
          ⟨root v, IntermediateField.subset_adjoin E (Set.range root) ⟨v, rfl⟩⟩
        let ζC : C := ⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩
        let β₂ : F :=
          ⟨root (Sum.inr (0 : Fin 2)),
            (show M ≤ F from le_sup_left)
              (IntermediateField.subset_adjoin E (Set.range root)
                ⟨Sum.inr (0 : Fin 2), rfl⟩)⟩
        let ζ₃ : E := IsCyclotomicExtension.zeta 3 ℚ E
        let z : F := algebraMap E F ξ
        Normal ℚ F ∧
        ∃ gcoord : I → Multiplicative (ZMod 3),
          (∀ v, ζ₃ ^ (Multiplicative.toAdd (gcoord v)).val = target v) ∧
        ∃ e : (F ≃ₐ[E] F) ≃* ((M ≃ₐ[E] M) × (C ≃ₐ[E] C)),
          ∃ gM : M ≃ₐ[E] M, ∃ σa : C ≃ₐ[E] C, ∃ gF : F ≃ₐ[E] F,
            e gF = (gM, σa) ∧
            (∀ v, gM (β v) = algebraMap E M (target v) * β v) ∧
            σa ζC = ζC ^ a.val.val ∧
            (∀ x : M', gF (x : F) = ((aM.autCongr gM x : M') : F)) ∧
            (∀ x : C', gF (x : F) = ((aC.autCongr σa x : C') : F)) ∧
            Module.finrank E F =
              3 ^ (2 * (D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.support j).card + 2) * Module.finrank E C ∧
            ∃ hNF : NumberField F, ∃ hGal : IsGalois ℚ F,
              letI : NumberField F := hNF
              letI : IsGalois ℚ F := hGal
              gF β₂ = z ^ 2 * β₂ ∧
              IsCyclotomicExtension {modulus j} ℚ C ∧
              (∀ (𝔭 : Ideal (𝓞 ℚ)) (_ : 𝔭.IsPrime)
                  (_ : Chebotarev.UnramifiedIn ℚ F 𝔭)
                  (hcop : (Ideal.absNorm 𝔭).Coprime (modulus j)),
                  Chebotarev.frobeniusClass ℚ F 𝔭 =
                    ConjClasses.mk (gF.restrictScalars ℚ) →
                  ZMod.unitOfCoprime (Ideal.absNorm 𝔭) hcop = a) ∧
            ∃ (c : F ≃ₐ[ℚ] F) (τ : E ≃ₐ[ℚ] E),
              τ ≠ 1 ∧
              (∀ x : E, c (algebraMap E F x) = algebraMap E F (τ x)) ∧
              let gQ : F ≃ₐ[ℚ] F := gF.restrictScalars ℚ
              let θ : F ≃ₐ[ℚ] F := c * gQ * c⁻¹
              θ β₂ = z * β₂ ∧ θ ≠ gQ ∧
                conjugatesOf gQ = {gQ, θ} ∧
                (conjugatesOf gQ).encard = 2 ∧
                Nat.card (ConjClasses.mk gQ).carrier = 2 ∧
                Nat.card (F ≃ₐ[ℚ] F) =
                  Nat.totient (modulus j) *
                    3 ^ (2 * (support j).card + 2) ∧
                ∃ hGalM : IsGalois E M, ∃ hFiniteM : FiniteDimensional E M,
                letI : IsGalois E M := hGalM
                letI : FiniteDimensional E M := hFiniteM
                letI : NumberField M := NumberField.of_module_finite E M
                let fp : Nat.Primes → Ideal (𝓞 ℚ) :=
                  fun p => Ideal.span {((p.1 : ℕ) : 𝓞 ℚ)}
                let T : Set Nat.Primes :=
                  {p | (p.1 : ZMod (modulus j)) = a.val ∧
                    ∃ (qE : Ideal (𝓞 E)), qE.IsPrime ∧
                      qE.LiesOver (Ideal.span {((p.1 : ℕ) : ℤ)}) ∧
                      ∃ (qM : Ideal (𝓞 M)), qM.IsPrime ∧ qM.LiesOver qE ∧
                        IsArithFrobAt (𝓞 E) gM qM}
                let T_unr : Set Nat.Primes :=
                  {p | (p.1 : ZMod (modulus j)) = a.val ∧
                    ∃ (qE : Ideal (𝓞 E)), qE.IsPrime ∧
                      qE.LiesOver (Ideal.span {((p.1 : ℕ) : ℤ)}) ∧
                      Chebotarev.UnramifiedIn E M qE ∧
                      ∃ (qM : Ideal (𝓞 M)), qM.IsPrime ∧ qM.LiesOver qE ∧
                        IsArithFrobAt (𝓞 E) gM qM}
                let U : Set (Ideal (𝓞 ℚ)) := fp '' T
                let R : Set (Ideal (𝓞 ℚ)) :=
                  {q | q.IsPrime ∧ q ≠ ⊥ ∧ ¬ Chebotarev.UnramifiedIn ℚ F q}
                let Sgood : Set (Ideal (𝓞 ℚ)) :=
                  {q | q.IsPrime ∧ Chebotarev.UnramifiedIn ℚ F q ∧
                    Chebotarev.frobeniusClass ℚ F q = ConjClasses.mk gQ ∧
                    (Ideal.absNorm q).Coprime (modulus j)}
                Sgood = U \ R ∧
                (∀ p : Nat.Primes, Ideal.absNorm (fp p) = p.1) ∧
                (∀ p : Nat.Primes, (fp p).IsPrime) ∧
                (∀ p : Nat.Primes, fp p ≠ ⊥) ∧
                Function.Injective fp ∧
                (∀ I : Ideal (𝓞 ℚ), I.IsPrime → I ≠ ⊥ →
                  ∃ p : Nat.Primes, fp p = I) ∧
                (∀ (p : Nat.Primes) (qE : Ideal (𝓞 E)),
                  qE.LiesOver (Ideal.span {((p.1 : ℕ) : ℤ)}) →
                  qE.LiesOver (fp p))

theorem actual_prime_transfer_data (j : ℕ) (a : (ZMod (modulus j))ˣ)
    (ha : ZMod.unitsMap (show 3 ∣ modulus j by
      refine ⟨80 * 3 ^ (j + 1), ?_⟩
      simp [modulus, pow_succ, mul_assoc, mul_comm]) a = 1) :
    ActualConjugacyData j a → ActualPrimeTransferData j a := by
  intro hconj
  classical
  letI : IsCyclotomicExtension {3} ℚ E :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  letI : IsGalois ℚ E := IsCyclotomicExtension.isGalois {3} ℚ E
  have hdiv : 3 ∣ modulus j := by
    refine ⟨80 * 3 ^ (j + 1), ?_⟩
    simp [modulus, pow_succ, mul_assoc, mul_comm]
  have ha' : ZMod.unitsMap hdiv a = 1 := ha
  dsimp only [ActualConjugacyData] at hconj
  obtain ⟨ζ, hζ, π, root, hdata, hEuler, hactualDisj, hFnormal,
    gcoord, hcoord, e, gM, σa, gF, heG, hgM, hσa,
    hpointM, hpointC, hdegF, hNF, hGal, hgfβ, hCcyclo, hres,
    c, τ, hτne, hcaction, hθβ, hθne, hclass, hcount, hclasscard, hgroupcard⟩ := hconj
  let φ : EisensteinOrder ≃ₐ[ℤ] 𝓞 E :=
    Classical.choice eisenstein_cyclotomic_equiv_exists
  let f : EisensteinOrder →+* E :=
    (algebraMap (𝓞 E) E).comp φ.toRingHom
  let ξ : E := f QuadraticAlgebra.omega
  let lam : EisensteinOrder := 1 + 2 * QuadraticAlgebra.omega
  let κ : {p : ℕ // p ∈ support j} → E := fun p =>
    f (localCubicSymbol (Ideal.span {π p.1}) lam)
  let target : radicalIndex j → E := Sum.elim
    (fun w => if w.2 then (κ w.1)⁻¹ ^ 2 else (κ w.1) ^ 2)
    (fun _ => ξ ^ 2)
  let M : IntermediateField E L := IntermediateField.adjoin E (Set.range root)
  let C : IntermediateField E L := actualCyclotomic ζ
  let F : IntermediateField E L := M ⊔ C
  let β : radicalIndex j → M := fun v =>
    ⟨root v, IntermediateField.subset_adjoin E (Set.range root) ⟨v, rfl⟩⟩
  let ζC : C := ⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩
  let M' : IntermediateField E F := IntermediateField.restrict (show M ≤ F from le_sup_left)
  let C' : IntermediateField E F := IntermediateField.restrict (show C ≤ F from le_sup_right)
  let aM : M ≃ₐ[E] M' := IntermediateField.restrictAlgEquiv (show M ≤ F from le_sup_left)
  let aC : C ≃ₐ[E] C' := IntermediateField.restrictAlgEquiv (show C ≤ F from le_sup_right)
  let β₂ : F :=
    ⟨root (Sum.inr (0 : Fin 2)),
      (show M ≤ F from le_sup_left)
        (IntermediateField.subset_adjoin E (Set.range root)
          ⟨Sum.inr (0 : Fin 2), rfl⟩)⟩
  let z : F := algebraMap E F ξ
  have hdegree : Module.finrank E M = 3 ^ (2 * (support j).card + 2) :=
    hdata.2.2.2.2.1
  letI : IsGalois E M := hdata.2.2.2.2.2.2.1
  letI : FiniteDimensional E M :=
    FiniteDimensional.of_finrank_pos (by rw [hdegree]; positivity)
  letI : NumberField M := NumberField.of_module_finite E M
  letI : NeZero (modulus j) := ⟨by simp [modulus]⟩
  letI : IsCyclotomicExtension {modulus j} E C :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
      (modulus j) E L C hζ).2 rfl
  letI : FiniteDimensional E C :=
    IsCyclotomicExtension.finiteDimensional {modulus j} E C
  letI : IsGalois E C := IsCyclotomicExtension.isGalois {modulus j} E C
  letI : FiniteDimensional E F := IntermediateField.finiteDimensional_sup M C
  letI : IsGalois E F := ⟨⟩
  letI : IsGalois E M' := IsGalois.of_algEquiv aM
  letI : IsGalois E C' := IsGalois.of_algEquiv aC
  letI : NumberField F := hNF
  letI : IsGalois ℚ F := hGal
  letI : IsCyclotomicExtension {modulus j} ℚ C := hCcyclo
  letI : NumberField C := IsCyclotomicExtension.numberField {modulus j} ℚ C
  let gQ : F ≃ₐ[ℚ] F := gF.restrictScalars ℚ
  let θ : F ≃ₐ[ℚ] F := c * gQ * c⁻¹
  let ζ₃ : E := IsCyclotomicExtension.zeta 3 ℚ E
  let ζF : F := ((aC ζC : C') : F)
  have hζCL : IsPrimitiveRoot (algebraMap C L ζC) (modulus j) := by
    simpa [ζC] using hζ
  have hζC : IsPrimitiveRoot ζC (modulus j) :=
    hζCL.of_map_of_injective (algebraMap C L).injective
  have hζC' : IsPrimitiveRoot (aC ζC) (modulus j) :=
    hζC.map_of_injective aC.injective
  have hζF : IsPrimitiveRoot ζF (modulus j) :=
    hζC'.map_of_injective (algebraMap C' F).injective
  have hact : gQ ζF = ζF ^ a.val.val := by
    calc
      gQ ζF = gF ((aC ζC : C') : F) := rfl
      _ = ((aC.autCongr σa (aC ζC) : C') : F) := hpointC (aC ζC)
      _ = ((aC (σa ζC) : C') : F) := by
        congr 1
        change aC (σa (aC.symm (aC ζC))) = aC (σa ζC)
        rw [aC.symm_apply_apply]
      _ = ζF ^ a.val.val := by
        rw [hσa, map_pow, IntermediateField.coe_pow]
  letI : IsCyclotomicExtension {modulus j} E C' :=
    IsCyclotomicExtension.equiv {modulus j} E C aC
  let σC : C' ≃ₐ[E] C' := aC.autCongr σa
  let fp : Nat.Primes → Ideal (𝓞 ℚ) :=
    fun p => Ideal.span {((p.1 : ℕ) : 𝓞 ℚ)}
  let T : Set Nat.Primes :=
    {p | (p.1 : ZMod (modulus j)) = a.val ∧
      ∃ (qE : Ideal (𝓞 E)), qE.IsPrime ∧
        qE.LiesOver (Ideal.span {((p.1 : ℕ) : ℤ)}) ∧
        ∃ (qM : Ideal (𝓞 M)), qM.IsPrime ∧ qM.LiesOver qE ∧
          IsArithFrobAt (𝓞 E) gM qM}
  let T_unr : Set Nat.Primes :=
    {p | (p.1 : ZMod (modulus j)) = a.val ∧
      ∃ (qE : Ideal (𝓞 E)), qE.IsPrime ∧
        qE.LiesOver (Ideal.span {((p.1 : ℕ) : ℤ)}) ∧
        Chebotarev.UnramifiedIn E M qE ∧
        ∃ (qM : Ideal (𝓞 M)), qM.IsPrime ∧ qM.LiesOver qE ∧
          IsArithFrobAt (𝓞 E) gM qM}
  let U : Set (Ideal (𝓞 ℚ)) := fp '' T
  let R : Set (Ideal (𝓞 ℚ)) :=
    {q | q.IsPrime ∧ q ≠ ⊥ ∧ ¬ Chebotarev.UnramifiedIn ℚ F q}
  let Sgood : Set (Ideal (𝓞 ℚ)) :=
    {q | q.IsPrime ∧ Chebotarev.UnramifiedIn ℚ F q ∧
      Chebotarev.frobeniusClass ℚ F q = ConjClasses.mk gQ ∧
      (Ideal.absNorm q).Coprime (modulus j)}
  have hnorm (p : Nat.Primes) : Ideal.absNorm (fp p) = p.1 := by
    simp only [fp, Ideal.absNorm_span_natCast,
      NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]
  have hprime (p : Nat.Primes) : (fp p).IsPrime := by
    have hpZ : (Ideal.span {((p.1 : ℕ) : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).2
        (Nat.prime_iff_prime_int.mp p.2)
    letI : (Ideal.span {((p.1 : ℕ) : ℤ)}).IsPrime := hpZ
    have hpMap :
        ((Ideal.span {((p.1 : ℕ) : ℤ)}).map
          Rat.ringOfIntegersEquiv.symm).IsPrime := inferInstance
    simpa only [fp, Ideal.map_span, Set.image_singleton, map_natCast] using hpMap
  have hnonzero (p : Nat.Primes) : fp p ≠ ⊥ := by
    intro heq
    have hz : p.1 = 0 := by simpa [heq] using (hnorm p).symm
    exact p.2.ne_zero hz
  have hinj : Function.Injective fp := by
    intro p q hpq
    apply Subtype.ext
    exact (hnorm p).symm.trans ((congrArg Ideal.absNorm hpq).trans (hnorm q))
  have hsurj : ∀ I : Ideal (𝓞 ℚ), I.IsPrime → I ≠ ⊥ →
      ∃ p, fp p = I := by
    intro I hIp hIne
    let J : Ideal ℤ := I.map Rat.ringOfIntegersEquiv
    have hJp : J.IsPrime := by
      letI : I.IsPrime := hIp
      exact inferInstance
    have hJne : J ≠ ⊥ := by
      intro hbot
      exact hIne ((Ideal.map_eq_bot_iff_of_injective
        Rat.ringOfIntegersEquiv.injective).mp hbot)
    rcases Ideal.isPrime_int_iff.mp hJp with hbot | ⟨p, hp, heq⟩
    · exact (hJne hbot).elim
    refine ⟨⟨p, hp⟩, ?_⟩
    have hundo :
        (I.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ)).map
          (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) = I := by
      rw [← RingEquiv.toRingHom_eq_coe, ← RingEquiv.toRingHom_eq_coe,
        Ideal.map_map, RingEquiv.toRingHom_eq_coe,
        RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp, Ideal.map_id]
    have hmap :
        (I.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ)).map
          (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) =
        (Ideal.span {((p : ℕ) : ℤ)}).map
          (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) := by
      exact congrArg
        (fun L : Ideal ℤ => L.map
          (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ)) heq
    rw [hundo] at hmap
    simpa only [fp, Ideal.map_span, Set.image_singleton, map_natCast] using hmap.symm
  have hQover (p : Nat.Primes) (qE : Ideal (𝓞 E))
      (hover : qE.LiesOver (Ideal.span {((p.1 : ℕ) : ℤ)})) :
      qE.LiesOver (fp p) := by
    let ringEquiv : ℤ ≃+* 𝓞 ℚ := Rat.ringOfIntegersEquiv.symm
    have hRingHom : (algebraMap ℤ (𝓞 ℚ)) =
        (ringEquiv : ℤ →+* 𝓞 ℚ) := RingHom.ext_int _ _
    have hMap : (Ideal.span {((p.1 : ℕ) : ℤ)}).map ringEquiv =
        fp p := by
      rw [Ideal.map_span, Set.image_singleton,
        show ringEquiv ((p.1 : ℕ) : ℤ) =
          ((p.1 : ℕ) : 𝓞 ℚ) by
          simpa only [Int.cast_natCast] using
            (eq_intCast ringEquiv ((p.1 : ℕ) : ℤ))]
    have hSpan : (fp p).under ℤ =
        Ideal.span {((p.1 : ℕ) : ℤ)} := by
      rw [← hMap, Ideal.under_def, hRingHom]
      exact (Ideal.span {((p.1 : ℕ) : ℤ)}).comap_map_of_bijective
        (ringEquiv : ℤ →+* 𝓞 ℚ) ringEquiv.bijective
    have hSurj : Function.Surjective (algebraMap ℤ (𝓞 ℚ)) := by
      rw [hRingHom]
      exact ringEquiv.surjective
    refine ⟨?_⟩
    apply Ideal.comap_injective_of_surjective
      (algebraMap ℤ (𝓞 ℚ)) hSurj
    change (fp p).under ℤ = (qE.under (𝓞 ℚ)).under ℤ
    rw [hSpan, Ideal.under_under]
    exact hover.over
  have hpmod3_of_mod (p : Nat.Primes)
      (hmod : (p.1 : ZMod (modulus j)) = a.val) :
      (p.1 : ZMod 3) = 1 := by
    have hc := congrArg
      (fun x : ZMod (modulus j) => (x.cast : ZMod 3)) hmod
    calc
      (p.1 : ZMod 3) = (a.val.cast : ZMod 3) := by
        simpa only [ZMod.cast_natCast hdiv] using hc
      _ = (ZMod.unitsMap hdiv a : ZMod 3) :=
        (ZMod.unitsMap_val hdiv a).symm
      _ = 1 := by rw [ha']; rfl
  have hcop_of_mod (p : Nat.Primes)
      (hmod : (p.1 : ZMod (modulus j)) = a.val) :
      p.1.Coprime (modulus j) := by
    apply (ZMod.isUnit_iff_coprime p.1 (modulus j)).mp
    rw [hmod]
    exact Units.isUnit a
  have hmod_of_res (p : Nat.Primes)
      (hcop : p.1.Coprime (modulus j))
      (hresP : ZMod.unitOfCoprime p.1 hcop = a) :
      (p.1 : ZMod (modulus j)) = a.val := by
    simpa only [ZMod.coe_unitOfCoprime] using congrArg Units.val hresP
  have hres_mod (p : Nat.Primes)
      (hunr : Chebotarev.UnramifiedIn ℚ F (fp p))
      (hcop : p.1.Coprime (modulus j))
      (hclass : Chebotarev.frobeniusClass ℚ F (fp p) =
        ConjClasses.mk gQ) :
      (p.1 : ZMod (modulus j)) = a.val := by
    letI : (fp p).IsPrime := hprime p
    have hr := hres (fp p) (hprime p) hunr
      ((hnorm p).symm ▸ hcop) hclass
    have hv := congrArg Units.val hr
    simpa only [ZMod.coe_unitOfCoprime, hnorm p] using hv
  have htop : M' ⊔ C' = ⊤ := by
    apply IntermediateField.lift_injective F
    rw [IntermediateField.lift_sup, IntermediateField.lift_restrict,
      IntermediateField.lift_restrict, IntermediateField.lift_top]
  let rM : (F ≃ₐ[E] F) →* (M' ≃ₐ[E] M') := AlgEquiv.restrictNormalHom M'
  let rC : (F ≃ₐ[E] F) →* (C' ≃ₐ[E] C') := AlgEquiv.restrictNormalHom C'
  let r : (F ≃ₐ[E] F) →* ((M' ≃ₐ[E] M') × (C' ≃ₐ[E] C')) := rM.prod rC
  have hrinj : Function.Injective r := by
    apply (injective_iff_map_eq_one r).2
    intro σ hσ
    have hm : σ ∈ rM.ker := by
      change rM σ = 1
      exact congrArg Prod.fst hσ
    have hc : σ ∈ rC.ker := by
      change rC σ = 1
      exact congrArg Prod.snd hσ
    have hm' : σ ∈ M'.fixingSubgroup := by
      rwa [← IntermediateField.restrictNormalHom_ker M']
    have hc' : σ ∈ C'.fixingSubgroup := by
      rwa [← IntermediateField.restrictNormalHom_ker C']
    have htopfix : σ ∈ (⊤ : IntermediateField E F).fixingSubgroup := by
      rw [← htop, IntermediateField.fixingSubgroup_sup]
      exact ⟨hm', hc'⟩
    simpa only [IntermediateField.fixingSubgroup_top, Subgroup.mem_bot] using htopfix
  have hrM : rM gF = aM.autCongr gM := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap M' F).injective
    exact (AlgEquiv.restrictNormal_commutes gF M' x).trans (hpointM x)
  have hrC : rC gF = aC.autCongr σa := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap C' F).injective
    exact (AlgEquiv.restrictNormal_commutes gF C' x).trans (hpointC x)
  have hcoords : Function.Injective
      (fun φ : F ≃ₐ[E] F =>
        (φ.restrictNormal M', φ.restrictNormal C')) := by
    change Function.Injective r
    exact hrinj
  have hcoordM : gF.restrictNormal M' = aM.autCongr gM := hrM
  have hcoordC : gF.restrictNormal C' = σC := hrC
  have hpow_of_mod (p : Nat.Primes)
      (hmod : (p.1 : ZMod (modulus j)) = a.val) :
      (aC ζC) ^ a.val.val = (aC ζC) ^ p.1 := by
    apply (hζC'.isOfFinOrder (NeZero.ne (modulus j))).pow_eq_pow_iff_modEq.mpr
    simpa only [← hζC'.eq_orderOf] using
      ((ZMod.natCast_eq_natCast_iff _ _ _).mp
        (by simpa only [ZMod.natCast_zmod_val] using hmod.symm))
  have hdegree_one (p : Nat.Primes)
      (hpmod3 : (p.1 : ZMod 3) = 1)
      (qE : Ideal (𝓞 E)) [qE.IsPrime]
      [qE.LiesOver (Ideal.span {((p.1 : ℕ) : ℤ)})] :
      Ideal.absNorm qE = p.1 := by
    letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
    have hpnot : ¬ p.1 ∣ 3 := by
      intro hdiv3
      have hpeq : p.1 = 3 :=
        (Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_three).mp hdiv3
      have hmod3 : ((3 : ℕ) : ZMod 3) = 1 := by
        simpa only [hpeq] using hpmod3
      have hzero : ((3 : ℕ) : ZMod 3) = 0 := by decide
      exact zero_ne_one (hzero.symm.trans hmod3)
    have hdeg : qE.inertiaDeg ℤ = 1 := by
      rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p.1 E qE hpnot]
      exact orderOf_eq_one_iff.mpr hpmod3
    letI : (Ideal.span {((p.1 : ℕ) : ℤ)}).IsMaximal := inferInstance
    letI : qE.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap qE
        (show (qE.under ℤ).IsMaximal by
          rw [← (inferInstance : qE.LiesOver
            (Ideal.span {((p.1 : ℕ) : ℤ)})).over]
          infer_instance)
    rw [Ideal.absNorm_eq_pow_inertiaDeg' qE p.2,
      Ideal.inertiaDeg'_eq_inertiaDeg
        (Ideal.span {((p.1 : ℕ) : ℤ)}) qE, hdeg, pow_one]
  have hForward (p : ℕ) (hp : p.Prime) (hpmod3 : (p : ZMod 3) = 1)
      (qQ : Ideal (𝓞 ℚ)) [qQ.IsPrime]
      (hqQ : qQ = Ideal.span {(p : 𝓞 ℚ)})
      (hunrQ : UnramifiedIn ℚ F qQ)
      (hcop : (Ideal.absNorm qQ).Coprime (modulus j))
      (hclass : frobeniusClass ℚ F qQ =
        ConjClasses.mk (gF.restrictScalars ℚ))
      (hres : ZMod.unitOfCoprime (Ideal.absNorm qQ) hcop = a) :
      (p : ZMod (modulus j)) = a.val ∧
        ∃ (qE : Ideal (𝓞 E)), qE.IsPrime ∧
          qE.LiesOver (Ideal.span {(p : ℤ)}) ∧
          ∃ (qM : Ideal (𝓞 M)), qM.IsPrime ∧ qM.LiesOver qE ∧
            IsArithFrobAt (𝓞 E) gM qM := by
    classical
    letI : NumberField M' := NumberField.of_intermediateField M'
    letI : IsScalarTower E M' F := M'.isScalarTower_mid'
    letI : IsScalarTower (𝓞 ℚ) (𝓞 E) (𝓞 F) := inferInstance
    letI : IsScalarTower (𝓞 E) (𝓞 M') (𝓞 F) := inferInstance
    have hQnorm : Ideal.absNorm qQ = p := by
      simp only [hqQ, Ideal.absNorm_span_natCast,
        NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]
    have hresP : (p : ZMod (modulus j)) = a.val := by
      simpa only [hQnorm, ZMod.coe_unitOfCoprime] using
        congrArg Units.val hres
    obtain ⟨qF₀, hF₀p, hF₀comap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 F) qQ (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp
          (FaithfulSMul.algebraMap_injective (𝓞 ℚ) (𝓞 F))]
        exact bot_le)
    have hF₀Q : qF₀.LiesOver qQ := ⟨hF₀comap.symm⟩
    letI : qF₀.IsPrime := hF₀p
    letI : Finite (𝓞 F ⧸ qF₀) :=
      Ideal.finiteQuotientOfFreeOfNeBot qF₀
        (Ideal.ne_bot_of_liesOver_of_ne_bot hunrQ.1 qF₀)
    let σQ : F ≃ₐ[ℚ] F := arithFrobAt (𝓞 ℚ) Gal(F/ℚ) qF₀
    have hσQ : IsArithFrobAt (𝓞 ℚ) σQ qF₀ :=
      IsArithFrobAt.arithFrobAt (𝓞 ℚ) Gal(F/ℚ) qF₀
    have hclassσ : frobeniusClass ℚ F qQ = ConjClasses.mk σQ := by
      let e : ∃ 𝔓 : Ideal (𝓞 F), 𝔓.IsPrime ∧ 𝔓.LiesOver qQ := by
        obtain ⟨𝔓, hp, hcomap⟩ :=
          Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 F) qQ (by
            rw [(RingHom.injective_iff_ker_eq_bot _).mp
              (FaithfulSMul.algebraMap_injective (𝓞 ℚ) (𝓞 F))]
            exact bot_le)
        exact ⟨𝔓, hp, ⟨hcomap.symm⟩⟩
      let 𝔓 := Classical.choose e
      letI : 𝔓.IsPrime := (Classical.choose_spec e).1
      have hlo : 𝔓.LiesOver qQ := (Classical.choose_spec e).2
      letI : Finite (𝓞 F ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
        (Ideal.ne_bot_of_liesOver_of_ne_bot hunrQ.1 𝔓)
      rw [frobeniusClass, dif_pos ⟨‹qQ.IsPrime›, hunrQ⟩]
      change ConjClasses.mk (arithFrobAt (𝓞 ℚ) Gal(F/ℚ) 𝔓) = ConjClasses.mk σQ
      exact ConjClasses.mk_eq_mk_iff_isConj.mpr <|
        isConj_arithFrobAt (𝓞 ℚ) Gal(F/ℚ) 𝔓 qF₀ (hlo.over.symm.trans hF₀Q.over)
    have hconj : IsConj σQ (gF.restrictScalars ℚ) :=
      ConjClasses.mk_eq_mk_iff_isConj.mp (hclassσ.symm.trans hclass)
    obtain ⟨t, ht⟩ := isConj_iff.mp hconj
    let qF : Ideal (𝓞 F) := t • qF₀
    letI : qF.IsPrime := inferInstance
    have hFQ : qF.LiesOver qQ := inferInstance
    letI : qF.LiesOver qQ := hFQ
    have hGQ : IsArithFrobAt (𝓞 ℚ) (gF.restrictScalars ℚ) qF := by
      rw [← ht]
      exact hσQ.conj t
    let qE : Ideal (𝓞 E) := qF.under (𝓞 E)
    letI : qE.IsPrime := inferInstance
    have hFE : qF.LiesOver qE := Ideal.over_under qF
    letI : qF.LiesOver qE := hFE
    have hEQ : qE.LiesOver qQ := Ideal.LiesOver.tower_bot qF qE qQ
    letI : qE.LiesOver qQ := hEQ
    let e : ℤ ≃+* 𝓞 ℚ := Rat.ringOfIntegersEquiv.symm
    have hRingHom : (algebraMap ℤ (𝓞 ℚ)) = (e : ℤ →+* 𝓞 ℚ) :=
      RingHom.ext_int _ _
    have hMap : (Ideal.span {(p : ℤ)}).map e =
        Ideal.span {(p : 𝓞 ℚ)} := by
      rw [Ideal.map_span, Set.image_singleton,
        show e (p : ℤ) = (p : 𝓞 ℚ) by
          simpa only [Int.cast_natCast] using (eq_intCast e (p : ℤ))]
    have hSpan : (Ideal.span {(p : 𝓞 ℚ)}).under ℤ =
        Ideal.span {(p : ℤ)} := by
      rw [← hMap, Ideal.under_def, hRingHom]
      exact (Ideal.span {(p : ℤ)}).comap_map_of_bijective
        (e : ℤ →+* 𝓞 ℚ) e.bijective
    have hEoverInt : qE.LiesOver (Ideal.span {(p : ℤ)}) := by
      refine ⟨?_⟩
      calc
        Ideal.span {(p : ℤ)} =
            (Ideal.span {(p : 𝓞 ℚ)}).under ℤ := hSpan.symm
        _ = (qE.under (𝓞 ℚ)).under ℤ := by rw [← hqQ, ← hEQ.over]
        _ = qE.under ℤ := Ideal.under_under qE
    letI : qE.LiesOver (Ideal.span {(p : ℤ)}) := hEoverInt
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    have hpnot : ¬ p ∣ 3 := by
      intro hdiv
      have hpeq : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdiv
      have hmod3 : ((3 : ℕ) : ZMod 3) = 1 := by
        simpa only [hpeq] using hpmod3
      have hzero : ((3 : ℕ) : ZMod 3) = 0 := by decide
      exact zero_ne_one (hzero.symm.trans hmod3)
    have hdeg : qE.inertiaDeg ℤ = 1 := by
      rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p E qE hpnot]
      exact orderOf_eq_one_iff.mpr hpmod3
    letI : (Ideal.span {(p : ℤ)}).IsMaximal := inferInstance
    letI : qE.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap qE
        (show (qE.under ℤ).IsMaximal by
          rw [← hEoverInt.over]
          infer_instance)
    have hEnorm : Ideal.absNorm qE = p := by
      rw [Ideal.absNorm_eq_pow_inertiaDeg' qE hp,
        Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p : ℤ)}) qE,
        hdeg, pow_one]
    have hCard : Nat.card (𝓞 E ⧸ qF.under (𝓞 E)) =
        Nat.card (𝓞 ℚ ⧸ qF.under (𝓞 ℚ)) := by
      rw [← hFE.over, ← hFQ.over]
      simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using
        hEnorm.trans hQnorm.symm
    have hActQ (x : 𝓞 F) : (gF.restrictScalars ℚ) • x = gF • x :=
      Subtype.ext (by
        change (gF.restrictScalars ℚ) • (x : F) = gF • (x : F)
        rw [AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.restrictScalars_apply])
    have hGE : IsArithFrobAt (𝓞 E) gF qF := by
      intro x
      change gF • x - x ^ Nat.card (𝓞 E ⧸ qF.under (𝓞 E)) ∈ qF
      have hq := hGQ x
      change (gF.restrictScalars ℚ) • x -
        x ^ Nat.card (𝓞 ℚ ⧸ qF.under (𝓞 ℚ)) ∈ qF at hq
      rw [hCard, ← hActQ]
      exact hq
    have hAct (T : IntermediateField E F) [IsGalois E T]
        (σ : F ≃ₐ[E] F) (y : 𝓞 T) :
        σ • (algebraMap (𝓞 T) (𝓞 F) y) =
          algebraMap (𝓞 T) (𝓞 F) ((σ.restrictNormal T) • y) := by
      letI : NumberField T := NumberField.of_intermediateField T
      letI : IsScalarTower E T F := T.isScalarTower_mid'
      have hbridgeF : ∀ (g : F ≃ₐ[E] F) (x : 𝓞 F),
          ((g • x : 𝓞 F) : F) = g • (x : F) := fun g x ↦ by rfl
      have hbridgeT : ∀ (g : T ≃ₐ[E] T) (z : 𝓞 T),
          ((g • z : 𝓞 T) : T) = g • (z : T) := fun g z ↦ by rfl
      have hcoe : ∀ z : 𝓞 T,
          ((algebraMap (𝓞 T) (𝓞 F) z : 𝓞 F) : F) = algebraMap T F (z : T) :=
        fun z ↦ by
          rw [RingOfIntegers.coe_eq_algebraMap,
            ← IsScalarTower.algebraMap_apply (𝓞 T) (𝓞 F) F,
            RingOfIntegers.coe_eq_algebraMap,
            ← IsScalarTower.algebraMap_apply (𝓞 T) T F]
      rw [RingOfIntegers.ext_iff]
      change ((σ • algebraMap (𝓞 T) (𝓞 F) y : 𝓞 F) : F) =
        ((algebraMap (𝓞 T) (𝓞 F) ((σ.restrictNormal T) • y) : 𝓞 F) : F)
      rw [hbridgeF, hcoe y, hcoe ((σ.restrictNormal T) • y), hbridgeT,
        AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.restrictNormal_commutes]
    have hDown (T : IntermediateField E F) [IsGalois E T]
        (σ : F ≃ₐ[E] F) (q : Ideal (𝓞 F))
        (hσ : IsArithFrobAt (𝓞 E) σ q) :
        IsArithFrobAt (𝓞 E) (σ.restrictNormal T) (q.under (𝓞 T)) := by
      letI : NumberField T := NumberField.of_intermediateField T
      letI : IsScalarTower E T F := T.isScalarTower_mid'
      intro y
      rw [Ideal.under_under q, Ideal.under, Ideal.mem_comap, map_sub, map_pow,
        show (MulSemiringAction.toAlgHom (𝓞 E) (𝓞 T) (σ.restrictNormal T)) y =
            (σ.restrictNormal T) • y from rfl,
        ← hAct T σ y]
      exact hσ (algebraMap (𝓞 T) (𝓞 F) y)
    let qM' : Ideal (𝓞 M') := qF.under (𝓞 M')
    letI : qM'.IsPrime := inferInstance
    have hFM : qF.LiesOver qM' := Ideal.over_under qF
    letI : qF.LiesOver qM' := hFM
    have hME : qM'.LiesOver qE := Ideal.LiesOver.tower_bot qF qM' qE
    letI : qM'.LiesOver qE := hME
    have hGM' : IsArithFrobAt (𝓞 E) (aM.autCongr gM) qM' := by
      have h := hDown M' gF qF hGE
      rwa [← hFM.over, hcoordM] at h
    let i : (𝓞 M) ≃ₐ[𝓞 E] (𝓞 M') := RingOfIntegers.mapAlgEquiv aM
    let qM : Ideal (𝓞 M) := qM'.map i.symm
    letI : qM.IsPrime := inferInstance
    have hMover : qM.LiesOver qE := by
      dsimp [qM]
      infer_instance
    letI : qM.LiesOver qE := hMover
    have hMcard : Nat.card (𝓞 E ⧸ qM.under (𝓞 E)) =
        Nat.card (𝓞 E ⧸ qM'.under (𝓞 E)) := by
      rw [← hMover.over, ← hME.over]
    have hIntertwine (x : 𝓞 M) :
        i (gM • x) = (aM.autCongr gM) • (i x) := by
      apply Subtype.ext
      change aM (gM (x : M)) =
        (aM.autCongr gM) (aM (x : M))
      change aM (gM (x : M)) =
        aM (gM (aM.symm (aM (x : M))))
      rw [aM.symm_apply_apply]
    have hBack (x : 𝓞 M) :
        i.symm ((aM.autCongr gM) • (i x)) = gM • x := by
      apply i.injective
      simpa only [i.apply_symm_apply] using (hIntertwine x).symm
    have hGM : IsArithFrobAt (𝓞 E) gM qM := by
      intro x
      change gM • x - x ^ Nat.card (𝓞 E ⧸ qM.under (𝓞 E)) ∈ qM
      have hy : (aM.autCongr gM) • i x -
          (i x) ^ Nat.card (𝓞 E ⧸ qM'.under (𝓞 E)) ∈ qM' :=
        hGM' (i x)
      have hx : i.symm ((aM.autCongr gM) • i x -
          (i x) ^ Nat.card (𝓞 E ⧸ qM'.under (𝓞 E))) ∈ qM :=
        Ideal.mem_map_of_mem i.symm hy
      simpa only [map_sub, map_pow, hBack,
        i.symm_apply_apply, hMcard] using hx
    exact ⟨hresP, qE, inferInstance, hEoverInt,
      qM, inferInstance, hMover, hGM⟩

  have hReverse (ζ : C') (hζ : IsPrimitiveRoot ζ (modulus j))
      (p : ℕ) (qQ : Ideal (𝓞 ℚ)) [qQ.IsPrime]
      (hqQ : qQ = Ideal.span {(p : 𝓞 ℚ)})
      (hunrQ : UnramifiedIn ℚ F qQ)
      (qE : Ideal (𝓞 E)) [qE.IsPrime]
      [qE.LiesOver (Ideal.span {(p : ℤ)})]
      (qM : Ideal (𝓞 M)) [qM.IsPrime] [qM.LiesOver qE]
      (hM : IsArithFrobAt (𝓞 E) gM qM)
      (hdegreeOne : Ideal.absNorm qE = Ideal.absNorm qQ)
      (hcop : (Ideal.absNorm qE).Coprime (modulus j))
      (hσC : σC ζ = ζ ^ Ideal.absNorm qE) :
      frobeniusClass ℚ F qQ =
        ConjClasses.mk (gF.restrictScalars ℚ) := by
    classical
    letI : NumberField M' := NumberField.of_intermediateField M'
    letI : NumberField C' := NumberField.of_intermediateField C'
    letI : IsScalarTower E M' F := M'.isScalarTower_mid'
    letI : IsScalarTower E C' F := C'.isScalarTower_mid'
    letI : IsScalarTower (𝓞 ℚ) (𝓞 E) (𝓞 F) := inferInstance
    letI : IsScalarTower (𝓞 E) (𝓞 M') (𝓞 F) := inferInstance
    letI : IsScalarTower (𝓞 E) (𝓞 C') (𝓞 F) := inferInstance
    let e : ℤ ≃+* 𝓞 ℚ := Rat.ringOfIntegersEquiv.symm
    have hRingHom : (algebraMap ℤ (𝓞 ℚ)) = (e : ℤ →+* 𝓞 ℚ) :=
      RingHom.ext_int _ _
    have hMap : (Ideal.span {(p : ℤ)}).map e =
        Ideal.span {(p : 𝓞 ℚ)} := by
      rw [Ideal.map_span, Set.image_singleton,
        show e (p : ℤ) = (p : 𝓞 ℚ) by
          simpa only [Int.cast_natCast] using (eq_intCast e (p : ℤ))]
    have hSpan : (Ideal.span {(p : 𝓞 ℚ)}).under ℤ =
        Ideal.span {(p : ℤ)} := by
      rw [← hMap, Ideal.under_def, hRingHom]
      exact (Ideal.span {(p : ℤ)}).comap_map_of_bijective
        (e : ℤ →+* 𝓞 ℚ) e.bijective
    have hSurj : Function.Surjective (algebraMap ℤ (𝓞 ℚ)) := by
      rw [hRingHom]
      exact e.surjective
    have hEQ : qE.LiesOver qQ := by
      rw [hqQ]
      refine ⟨?_⟩
      apply Ideal.comap_injective_of_surjective
        (algebraMap ℤ (𝓞 ℚ)) hSurj
      change (Ideal.span {(p : 𝓞 ℚ)}).under ℤ =
        (qE.under (𝓞 ℚ)).under ℤ
      rw [hSpan, Ideal.under_under]
      exact (inferInstance : qE.LiesOver (Ideal.span {(p : ℤ)})).over
    letI : qE.LiesOver qQ := hEQ
    let i : (𝓞 M) ≃ₐ[𝓞 E] (𝓞 M') := RingOfIntegers.mapAlgEquiv aM
    let qM' : Ideal (𝓞 M') := qM.map i
    letI : qM'.IsPrime := inferInstance
    have hM'over : qM'.LiesOver qE := by
      dsimp [qM']
      infer_instance
    letI : qM'.LiesOver qE := hM'over
    have hMcard : Nat.card (𝓞 E ⧸ qM'.under (𝓞 E)) =
        Nat.card (𝓞 E ⧸ qM.under (𝓞 E)) := by
      rw [← (inferInstance : qM'.LiesOver qE).over,
        ← (inferInstance : qM.LiesOver qE).over]
    have hIntertwine (x : 𝓞 M) :
        i (gM • x) = (aM.autCongr gM) • (i x) := by
      apply Subtype.ext
      change aM (gM (x : M)) =
        (aM.autCongr gM) (aM (x : M))
      change aM (gM (x : M)) =
        aM (gM (aM.symm (aM (x : M))))
      rw [aM.symm_apply_apply]
    have hM' : IsArithFrobAt (𝓞 E) (aM.autCongr gM) qM' := by
      intro y
      change (aM.autCongr gM) • y -
        y ^ Nat.card (𝓞 E ⧸ qM'.under (𝓞 E)) ∈ qM'
      have hx : i (gM • i.symm y -
            (i.symm y) ^ Nat.card (𝓞 E ⧸ qM.under (𝓞 E))) ∈ qM' :=
        Ideal.mem_map_of_mem i (hM (i.symm y))
      simpa only [map_sub, map_pow, hIntertwine, hMcard,
        i.apply_symm_apply] using hx
    have hEne : qE ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hunrQ.1 qE
    have hMne : qM' ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hEne qM'
    obtain ⟨qF, hFp, hFcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 F) qM' (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp
          (FaithfulSMul.algebraMap_injective (𝓞 M') (𝓞 F))]
        exact bot_le)
    have hFM : qF.LiesOver qM' := ⟨hFcomap.symm⟩
    have hFne : qF ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hMne qF
    letI : qF.IsPrime := hFp
    letI : qF.LiesOver qM' := hFM
    have hFE : qF.LiesOver qE := Ideal.LiesOver.trans qF qM' qE
    letI : qF.LiesOver qE := hFE
    have hFQ : qF.LiesOver qQ := Ideal.LiesOver.trans qF qE qQ
    letI : qF.LiesOver qQ := hFQ
    letI : Finite (𝓞 F ⧸ qF) := Ideal.finiteQuotientOfFreeOfNeBot qF hFne
    let φ : F ≃ₐ[E] F := arithFrobAt (𝓞 E) Gal(F/E) qF
    have hφ : IsArithFrobAt (𝓞 E) φ qF :=
      IsArithFrobAt.arithFrobAt (𝓞 E) Gal(F/E) qF
    have hAct (T : IntermediateField E F) [IsGalois E T]
        (σ : F ≃ₐ[E] F) (y : 𝓞 T) :
        σ • (algebraMap (𝓞 T) (𝓞 F) y) =
          algebraMap (𝓞 T) (𝓞 F) ((σ.restrictNormal T) • y) := by
      letI : NumberField T := NumberField.of_intermediateField T
      letI : IsScalarTower E T F := T.isScalarTower_mid'
      have hbridgeF : ∀ (g : F ≃ₐ[E] F) (x : 𝓞 F),
          ((g • x : 𝓞 F) : F) = g • (x : F) := fun g x ↦ by rfl
      have hbridgeT : ∀ (g : T ≃ₐ[E] T) (z : 𝓞 T),
          ((g • z : 𝓞 T) : T) = g • (z : T) := fun g z ↦ by rfl
      have hcoe : ∀ z : 𝓞 T,
          ((algebraMap (𝓞 T) (𝓞 F) z : 𝓞 F) : F) = algebraMap T F (z : T) :=
        fun z ↦ by
          rw [RingOfIntegers.coe_eq_algebraMap,
            ← IsScalarTower.algebraMap_apply (𝓞 T) (𝓞 F) F,
            RingOfIntegers.coe_eq_algebraMap,
            ← IsScalarTower.algebraMap_apply (𝓞 T) T F]
      rw [RingOfIntegers.ext_iff]
      change ((σ • algebraMap (𝓞 T) (𝓞 F) y : 𝓞 F) : F) =
        ((algebraMap (𝓞 T) (𝓞 F) ((σ.restrictNormal T) • y) : 𝓞 F) : F)
      rw [hbridgeF, hcoe y, hcoe ((σ.restrictNormal T) • y), hbridgeT,
        AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.restrictNormal_commutes]
    have hDown (T : IntermediateField E F) [IsGalois E T]
        (σ : F ≃ₐ[E] F) (q : Ideal (𝓞 F))
        (hσ : IsArithFrobAt (𝓞 E) σ q) :
        IsArithFrobAt (𝓞 E) (σ.restrictNormal T) (q.under (𝓞 T)) := by
      letI : NumberField T := NumberField.of_intermediateField T
      letI : IsScalarTower E T F := T.isScalarTower_mid'
      intro y
      rw [Ideal.under_under q, Ideal.under, Ideal.mem_comap, map_sub, map_pow,
        show (MulSemiringAction.toAlgHom (𝓞 E) (𝓞 T) (σ.restrictNormal T)) y =
            (σ.restrictNormal T) • y from rfl,
        ← hAct T σ y]
      exact hσ (algebraMap (𝓞 T) (𝓞 F) y)
    have hφM : IsArithFrobAt (𝓞 E) (φ.restrictNormal M') qM' := by
      have h := hDown M' φ qF hφ
      rwa [← hFM.over] at h
    haveI : Algebra.IsUnramifiedAt (𝓞 ℚ) qF :=
      hunrQ.2 qF ((inferInstance : qF.IsPrime).isMaximal hFne) hFQ
    haveI : Algebra.IsUnramifiedAt (𝓞 E) qF :=
      Algebra.IsUnramifiedAt.of_restrictScalars (𝓞 ℚ) qF
    haveI : Algebra.IsUnramifiedAt (𝓞 E) qM' :=
      Algebra.IsUnramifiedAt.of_liesOver (𝓞 E) qM' qF
    letI : Finite (𝓞 M' ⧸ qM') :=
      Ideal.finiteQuotientOfFreeOfNeBot qM' hMne
    letI : FaithfulSMul Gal(↥M'/E) (𝓞 M') := IsGaloisGroup.faithful (𝓞 E)
    have hφM_eq : φ.restrictNormal M' = aM.autCongr gM :=
      MulSemiringAction.toAlgHom_injective (𝓞 E) (𝓞 M') <|
        AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hφM hM'
          qM'.primeCompl_le_nonZeroDivisors
    let qC : Ideal (𝓞 C') := qF.under (𝓞 C')
    letI : qC.IsPrime := inferInstance
    have hFC : qF.LiesOver qC := Ideal.over_under qF
    letI : qF.LiesOver qC := hFC
    have hCE : qC.LiesOver qE := Ideal.LiesOver.tower_bot qF qC qE
    letI : qC.LiesOver qE := hCE
    have hφC : IsArithFrobAt (𝓞 E) (φ.restrictNormal C') qC := by
      exact hDown C' φ qF hφ
    have hCne : Ideal.absNorm qC ≠ 1 :=
      fun h => (inferInstance : qC.IsPrime).ne_top (Ideal.absNorm_eq_one_iff.mp h)
    have hCcop : (Ideal.absNorm qC).Coprime (modulus j) := by
      rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver qC qE
        (inferInstance : qE.IsPrime) hEne]
      exact Nat.Coprime.pow_left _ hcop
    have hmnotmem : ((modulus j) : 𝓞 C') ∉ qC := by
      intro hmem
      have hd := Ideal.absNorm_dvd_absNorm_of_le
        ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
      rw [Ideal.absNorm_span_singleton,
        show (((modulus j) : ℕ) : 𝓞 C') = algebraMap ℤ (𝓞 C') ((modulus j) : ℤ) by push_cast; rfl,
        Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at hd
      exact hCne ((hCcop.pow_right _).eq_one_of_dvd hd)
    have hCardC : Ideal.absNorm qE =
        Nat.card (𝓞 E ⧸ qC.under (𝓞 E)) := by
      rw [show qE = qC.under (𝓞 E) from hCE.over,
        Ideal.absNorm_apply, Submodule.cardQuot_apply]
    let z : 𝓞 C' := hζ.toInteger
    have hkey := hφC.apply_of_pow_eq_one
      hζ.toInteger_isPrimitiveRoot.pow_eq_one hmnotmem
    rw [← hCardC] at hkey
    have hmap := congrArg (algebraMap (𝓞 C') C') hkey
    have hφζ : (φ.restrictNormal C') ζ = ζ ^ Ideal.absNorm qE := by
      rwa [map_pow,
        show (algebraMap (𝓞 C') C')
          ((MulSemiringAction.toAlgHom (𝓞 E) (𝓞 C') (φ.restrictNormal C')) z) =
            (φ.restrictNormal C') ζ from rfl,
        show (algebraMap (𝓞 C') C') z = ζ from rfl] at hmap
    have hφC_eq : φ.restrictNormal C' = σC := by
      apply IsCyclotomicExtension.algEquiv_eq_of_apply_eq (S := {(modulus j)})
      intro n hn hn0
      have hnm : n = (modulus j) := Set.mem_singleton_iff.mp hn
      subst n
      exact ⟨ζ, hζ, hφζ.trans hσC.symm⟩
    have hφeq : φ = gF := by
      apply hcoords
      exact Prod.ext (hφM_eq.trans hcoordM.symm)
        (hφC_eq.trans hcoordC.symm)
    have hCardQ : Nat.card (𝓞 E ⧸ qF.under (𝓞 E)) =
        Nat.card (𝓞 ℚ ⧸ qF.under (𝓞 ℚ)) := by
      rw [← hFE.over, ← hFQ.over]
      simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using hdegreeOne
    have hActQ (x : 𝓞 F) : (φ.restrictScalars ℚ) • x = φ • x :=
      Subtype.ext (by
        change (φ.restrictScalars ℚ) • (x : F) = φ • (x : F)
        rw [AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.restrictScalars_apply])
    have hφQ : IsArithFrobAt (𝓞 ℚ) (φ.restrictScalars ℚ) qF := by
      intro x
      change (φ.restrictScalars ℚ) • x -
        x ^ Nat.card (𝓞 ℚ ⧸ qF.under (𝓞 ℚ)) ∈ qF
      have he := hφ x
      change φ • x - x ^ Nat.card (𝓞 E ⧸ qF.under (𝓞 E)) ∈ qF at he
      rw [← hCardQ, hActQ]
      exact he
    rw [hφeq] at hφQ
    letI : FaithfulSMul Gal(↥F/ℚ) (𝓞 F) := IsGaloisGroup.faithful (𝓞 ℚ)
    have hφQ_eq : gF.restrictScalars ℚ = arithFrobAt (𝓞 ℚ) Gal(F/ℚ) qF :=
      MulSemiringAction.toAlgHom_injective (𝓞 ℚ) (𝓞 F) <|
        AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hφQ
          (IsArithFrobAt.arithFrobAt (𝓞 ℚ) Gal(F/ℚ) qF)
          qF.primeCompl_le_nonZeroDivisors
    let e : ∃ 𝔓 : Ideal (𝓞 F), 𝔓.IsPrime ∧ 𝔓.LiesOver qQ := by
      obtain ⟨𝔓, hp, hcomap⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 F) qQ (by
          rw [(RingHom.injective_iff_ker_eq_bot _).mp
            (FaithfulSMul.algebraMap_injective (𝓞 ℚ) (𝓞 F))]
          exact bot_le)
      exact ⟨𝔓, hp, ⟨hcomap.symm⟩⟩
    let 𝔓 := Classical.choose e
    letI : 𝔓.IsPrime := (Classical.choose_spec e).1
    have hlo : 𝔓.LiesOver qQ := (Classical.choose_spec e).2
    letI : Finite (𝓞 F ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
      (Ideal.ne_bot_of_liesOver_of_ne_bot hunrQ.1 𝔓)
    rw [frobeniusClass, dif_pos ⟨‹qQ.IsPrime›, hunrQ⟩, hφQ_eq]
    change ConjClasses.mk (arithFrobAt (𝓞 ℚ) Gal(F/ℚ) 𝔓) =
      ConjClasses.mk (arithFrobAt (𝓞 ℚ) Gal(F/ℚ) qF)
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr <|
      isConj_arithFrobAt (𝓞 ℚ) Gal(F/ℚ) 𝔓 qF (hlo.over.symm.trans hFQ.over)

  have hgood_eq : Sgood = U \ R := by
    ext q
    constructor
    · intro hq
      have hqp : q.IsPrime := hq.1
      have hunr : Chebotarev.UnramifiedIn ℚ F q := hq.2.1
      have hclass : Chebotarev.frobeniusClass ℚ F q =
          ConjClasses.mk gQ := hq.2.2.1
      have hcop : (Ideal.absNorm q).Coprime (modulus j) := hq.2.2.2
      obtain ⟨p, rfl⟩ := hsurj q hqp hunr.1
      letI : (fp p).IsPrime := hprime p
      have hcopP : p.1.Coprime (modulus j) := (hnorm p) ▸ hcop
      have hresP : ZMod.unitOfCoprime (Ideal.absNorm (fp p))
          ((hnorm p).symm ▸ hcopP) = a :=
        hres (fp p) (hprime p) hunr
          ((hnorm p).symm ▸ hcopP) hclass
      have hmod : (p.1 : ZMod (modulus j)) = a.val :=
        hres_mod p hunr hcopP hclass
      have hpmod3 : (p.1 : ZMod 3) = 1 := hpmod3_of_mod p hmod
      obtain ⟨_, qE, hqE, hoverE, qM, hqM, hoverM, hfrobM⟩ :=
        hForward p.1 p.2 hpmod3 (fp p) (by rfl)
          hunr ((hnorm p).symm ▸ hcopP) hclass hresP
      refine ⟨⟨p, ⟨hmod, qE, hqE, hoverE,
        qM, hqM, hoverM, hfrobM⟩, rfl⟩, ?_⟩
      intro hram
      exact hram.2.2 hunr
    · rintro ⟨⟨p, hpT, rfl⟩, hnotR⟩
      have hpmod : (p.1 : ZMod (modulus j)) = a.val := hpT.1
      obtain ⟨qE, hqE, hoverE, qM, hqM, hoverM, hM⟩ := hpT.2
      letI : (fp p).IsPrime := hprime p
      letI : qE.IsPrime := hqE
      letI : qE.LiesOver (Ideal.span {((p.1 : ℕ) : ℤ)}) := hoverE
      letI : qM.IsPrime := hqM
      letI : qM.LiesOver qE := hoverM
      have hunr : Chebotarev.UnramifiedIn ℚ F (fp p) := by
        by_contra hn
        exact hnotR ⟨hprime p, hnonzero p, hn⟩
      have hpmod3 : (p.1 : ZMod 3) = 1 := hpmod3_of_mod p hpmod
      have hnormE : Ideal.absNorm qE = p.1 := hdegree_one p hpmod3 qE
      have hdegree : Ideal.absNorm qE = Ideal.absNorm (fp p) :=
        hnormE.trans (hnorm p).symm
      have hcopP : p.1.Coprime (modulus j) := hcop_of_mod p hpmod
      have hcopE : (Ideal.absNorm qE).Coprime (modulus j) :=
        hnormE.symm ▸ hcopP
      have hσC : σC (aC ζC) = (aC ζC) ^ Ideal.absNorm qE := by
        calc
          σC (aC ζC) = aC (σa ζC) := by
            change aC (σa (aC.symm (aC ζC))) = aC (σa ζC)
            rw [aC.symm_apply_apply]
          _ = (aC ζC) ^ a.val.val := by rw [hσa, map_pow]
          _ = (aC ζC) ^ p.1 := hpow_of_mod p hpmod
          _ = (aC ζC) ^ Ideal.absNorm qE := by rw [hnormE]
      have hclass : Chebotarev.frobeniusClass ℚ F (fp p) =
          ConjClasses.mk gQ :=
        hReverse (aC ζC) hζC' p.1 (fp p) (by rfl) hunr qE qM
          hM hdegree hcopE hσC
      exact ⟨hprime p, hunr, hclass,
        (hnorm p).symm ▸ hcopP⟩
  exact ⟨ζ, hζ, π, root, hdata, hEuler, hactualDisj, hFnormal,
    gcoord, hcoord, e, gM, σa, gF, heG, hgM, hσa,
    hpointM, hpointC, hdegF, hNF, hGal, hgfβ, hCcyclo, hres,
    c, τ, hτne, hcaction, hθβ, hθne, hclass, hcount,
    hclasscard, hgroupcard, (inferInstance : IsGalois E M),
    (inferInstance : FiniteDimensional E M), hgood_eq, hnorm, hprime,
    hnonzero, hinj, hsurj, hQover⟩
