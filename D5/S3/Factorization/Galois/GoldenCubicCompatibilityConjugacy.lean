/- GID: D5/S3/Factorization/Galois/GoldenCubicCompatibilityConjugacy
   generality: I
   mirror-B: D5/B/S3/Factorization/Galois/GoldenCubicCompatibilityConjugacy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual compatibility automorphism has a two-element rational conjugacy class and the stated Galois group order. -/
import D5.S3.Factorization.Galois.GoldenCubicCompatibilityCompositum
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

def ActualConjugacyData (j : ℕ) (a : (ZMod (modulus j))ˣ) : Prop :=
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
                    3 ^ (2 * (support j).card + 2)

theorem actual_conjugacy_data (j : ℕ) (a : (ZMod (modulus j))ˣ)
    (ha : ZMod.unitsMap (show 3 ∣ modulus j by
      refine ⟨80 * 3 ^ (j + 1), ?_⟩
      simp [modulus, pow_succ, mul_assoc, mul_comm]) a = 1) :
    ActualCompositumData j a → ActualConjugacyData j a := by
  intro hcomp
  classical
  letI : IsCyclotomicExtension {3} ℚ E :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  letI : IsGalois ℚ E := IsCyclotomicExtension.isGalois {3} ℚ E
  have hdiv : 3 ∣ modulus j := by
    refine ⟨80 * 3 ^ (j + 1), ?_⟩
    simp [modulus, pow_succ, mul_assoc, mul_comm]
  have ha' : ZMod.unitsMap hdiv a = 1 := ha
  dsimp only [ActualCompositumData] at hcomp
  obtain ⟨ζ, hζ, π, root, hdata, hEuler, hactualDisj, hFnormal,
    gcoord, hcoord, e, gM, σa, gF, heG, hgM, hσa,
    hpointM, hpointC, hdegF, hNF, hGal, hgfβ, hCcyclo, hres⟩ := hcomp
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
  letI : Normal ℚ F := hFnormal
  let e3 := IsCyclotomicExtension.Rat.galEquivZMod 3 E
  have hωpoly : (QuadraticAlgebra.omega : EisensteinOrder) ^ 2 +
      QuadraticAlgebra.omega + 1 = 0 := by
    rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_add]
    simp
  have hξpoly : ξ ^ 2 + ξ + 1 = 0 := by
    have h := congrArg f hωpoly
    simpa only [map_add, map_pow, map_one, map_zero, ξ] using h
  have hξ3 : ξ ^ 3 = 1 := by
    linear_combination (ξ - 1) * hξpoly
  have hξne : ξ ≠ 1 := by
    intro heq
    rw [heq] at hξpoly
    norm_num at hξpoly
  have hξ2ne : ξ ^ 2 ≠ 1 := by
    intro h2
    apply hξne
    calc
      ξ = ξ ^ 2 * ξ := by rw [h2]; ring
      _ = ξ ^ 3 := by ring
      _ = 1 := hξ3
  have hξprimitive : IsPrimitiveRoot ξ 3 := by
    refine (IsPrimitiveRoot.iff (by decide : 0 < 3)).2 ⟨hξ3, ?_⟩
    intro n hn hlt
    have hn' : n = 1 ∨ n = 2 := by omega
    rcases hn' with rfl | rfl
    · simpa only [pow_one] using hξne
    · exact hξ2ne
  let τ : E ≃ₐ[ℚ] E := e3.symm (-1)
  have hminus : (-1 : (ZMod 3)ˣ) ≠ 1 := by
    intro h
    have hv := congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) h
    exact (show (-1 : ZMod 3) ≠ 1 by decide) hv
  have hτne : τ ≠ 1 := by
    intro h
    apply hminus
    calc
      (-1 : (ZMod 3)ˣ) = e3 τ := (e3.apply_symm_apply _).symm
      _ = e3 1 := by rw [h]
      _ = 1 := map_one e3
  let c : F ≃ₐ[ℚ] F := τ.liftNormal F
  have hcaction (a : E) :
      c (algebraMap E F a) = algebraMap E F (τ a) :=
    τ.liftNormal_commutes F a
  have hz : IsPrimitiveRoot z 3 :=
    hξprimitive.map_of_injective (algebraMap E F).injective
  have hβcube : β₂ ^ 3 = (2 : F) := by
    apply Subtype.ext
    change root (Sum.inr (0 : Fin 2)) ^ 3 = (2 : L)
    simpa [NumberField.RingOfIntegers.coe_eq_algebraMap, map_ofNat]
      using hdata.2.2.2.1 (Sum.inr (0 : Fin 2))
  have hβne : β₂ ≠ 0 := by
    intro h
    have hc := hβcube
    rw [h, zero_pow (by decide)] at hc
    norm_num at hc
  let gQ : F ≃ₐ[ℚ] F := gF.restrictScalars ℚ
  let θ : F ≃ₐ[ℚ] F := c * gQ * c⁻¹
  have hσQβ : gQ β₂ = z ^ 2 * β₂ := by
    change gF β₂ = z ^ 2 * β₂
    exact hgfβ
  have hτξne : τ ξ ≠ ξ := by
    intro hfix
    apply hτne
    apply IsCyclotomicExtension.algEquiv_eq_of_apply_eq (S := {3})
    intro n hn hn0
    have hn3 : n = 3 := Set.mem_singleton_iff.mp hn
    subst n
    exact ⟨ξ, hξprimitive, by simpa using hfix⟩
  have hτξ : τ ξ = ξ⁻¹ := by
    have hτpow : (τ ξ) ^ 3 = 1 := by
      rw [← map_pow, hξprimitive.pow_eq_one, map_one]
    obtain ⟨k, hk, heq⟩ := hξprimitive.eq_pow_of_pow_eq_one hτpow
    have hz2 : ξ ^ 2 = ξ⁻¹ :=
      (mul_eq_one_iff_eq_inv₀ (hξprimitive.ne_zero (by decide))).mp
        (by simpa [pow_succ] using hξprimitive.pow_eq_one)
    interval_cases k
    · have h1 : τ ξ = 1 := by simpa using heq.symm
      exact False.elim
        ((hξprimitive.map_of_injective τ.injective).ne_one (by decide) h1)
    · exact False.elim (hτξne (by simpa using heq.symm))
    · simpa only [hz2] using heq.symm
  have hcz : c z = z⁻¹ := by
    simpa [z, hτξ, map_inv₀] using hcaction ξ
  have hgz : gQ z = z := by
    change gF z = z
    exact gF.commutes ξ
  have hcubed : (c β₂) ^ 3 = β₂ ^ 3 := by
    calc
      (c β₂) ^ 3 = c (β₂ ^ 3) := (map_pow c β₂ 3).symm
      _ = c (2 : F) := congrArg c hβcube
      _ = (2 : F) := map_ofNat c 2
      _ = β₂ ^ 3 := hβcube.symm
  have hphase : ∃ k : ℕ, k < 3 ∧ c β₂ = z ^ k * β₂ := by
    have hr : (c β₂ / β₂) ^ 3 = 1 := by
      rw [div_pow, hcubed, div_self (pow_ne_zero _ hβne)]
    obtain ⟨k, hk, hpow⟩ := hz.eq_pow_of_pow_eq_one hr
    refine ⟨k, hk, ?_⟩
    calc
      c β₂ = (c β₂ / β₂) * β₂ := (div_mul_cancel₀ _ hβne).symm
      _ = z ^ k * β₂ := by rw [← hpow]
  obtain ⟨kphase, hkphase, hkβ⟩ := hphase
  have hcInvz : c.symm z = z⁻¹ := by
    apply c.injective
    simp [hcz]
  have hθz : θ z = z := by
    simp [θ, AlgEquiv.mul_apply, hcInvz, hgz, hcz]
  have hθphase : θ (z ^ kphase) = z ^ kphase := by
    rw [map_pow, hθz]
  have hθcβ : θ (c β₂) = c (gQ β₂) := by
    simp [θ, AlgEquiv.mul_apply]
  have htwist : z ^ kphase * θ β₂ = z ^ kphase * ((z⁻¹) ^ 2 * β₂) := by
    calc
      z ^ kphase * θ β₂ = θ (z ^ kphase * β₂) := by
        rw [map_mul, hθphase]
      _ = θ (c β₂) := by rw [hkβ]
      _ = c (gQ β₂) := hθcβ
      _ = c (z ^ 2 * β₂) := by rw [hσQβ]
      _ = z ^ kphase * ((z⁻¹) ^ 2 * β₂) := by
        rw [map_mul, map_pow, hcz, hkβ]
        ring
  have hθβinv : θ β₂ = (z⁻¹) ^ 2 * β₂ :=
    mul_left_cancel₀ (pow_ne_zero _ (hz.ne_zero (by decide))) htwist
  have hz2 : z ^ 2 = z⁻¹ :=
    (mul_eq_one_iff_eq_inv₀ (hz.ne_zero (by decide))).mp
      (by simpa [pow_succ] using hz.pow_eq_one)
  have hzinvtwo : (z⁻¹) ^ 2 = z := by
    rw [← hz2, ← pow_mul]
    calc
      z ^ (2 * 2) = z ^ 3 * z := by ring
      _ = z := by rw [hz.pow_eq_one, one_mul]
  have hθβ : θ β₂ = z * β₂ := by
    rw [hθβinv, hzinvtwo]
  have hz_ne_zsq : z ≠ z ^ 2 := by
    intro h
    have h' : z * (1 : F) = z * z := by simpa [pow_two] using h
    have h1 : (1 : F) = z := mul_left_cancel₀ (hz.ne_zero (by decide)) h'
    exact hz.ne_one (by decide) h1.symm
  have hθne : θ ≠ gQ := by
    intro heq
    have heqβ := congrArg (fun u : F ≃ₐ[ℚ] F => u β₂) heq
    rw [hθβ, hσQβ] at heqβ
    exact hz_ne_zsq (mul_right_cancel₀ hβne heqβ)
  letI : IsMulCommutative (C ≃ₐ[E] C) :=
    IsCyclotomicExtension.isMulCommutative {modulus j} E C
  have hE2 : Module.finrank ℚ E = 2 := by
    rw [IsCyclotomicExtension.Rat.finrank 3 E]
    norm_num [Nat.totient_prime Nat.prime_three]
  let ι : (F ≃ₐ[E] F) →* (F ≃ₐ[ℚ] F) := AlgEquiv.restrictScalarsHom ℚ
  let H : Subgroup (F ≃ₐ[ℚ] F) := ι.range
  have hι : Function.Injective ι := AlgEquiv.restrictScalars_injective ℚ
  let eH : (F ≃ₐ[E] F) ≃ H := Equiv.ofBijective
    (fun σ => (⟨ι σ, ⟨σ, rfl⟩⟩ : H))
    (by
      constructor
      · intro x y h
        apply hι
        exact congrArg Subtype.val h
      · rintro ⟨x, ⟨σ, rfl⟩⟩
        exact ⟨σ, rfl⟩)
  have hcardH : Nat.card H = Nat.card (F ≃ₐ[E] F) :=
    (Nat.card_congr eH).symm
  have hcardG : Nat.card (F ≃ₐ[ℚ] F) =
      2 * Nat.card (F ≃ₐ[E] F) := by
    calc
      Nat.card (F ≃ₐ[ℚ] F) = Module.finrank ℚ F :=
        IsGalois.card_aut_eq_finrank ℚ F
      _ = Module.finrank ℚ E * Module.finrank E F :=
        (Module.finrank_mul_finrank ℚ E F).symm
      _ = 2 * Nat.card (F ≃ₐ[E] F) := by
        rw [hE2, IsGalois.card_aut_eq_finrank E F]
  have hindex : H.index = 2 := by
    have h := H.card_mul_index
    rw [hcardH, hcardG] at h
    have hpos : 0 < Nat.card (F ≃ₐ[E] F) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hpos
    exact h.trans (Nat.mul_comm 2 (Nat.card (F ≃ₐ[E] F)))
  obtain ⟨eM, _⟩ := hdata.2.2.2.2.2.2.2
  have hMcomm (x y : M ≃ₐ[E] M) : x * y = y * x := by
    apply eM.injective
    simpa only [map_mul] using mul_comm (eM x) (eM y)
  have hFcomm (x y : F ≃ₐ[E] F) : x * y = y * x := by
    apply e.injective
    rw [map_mul, map_mul]
    apply Prod.ext
    · change (e x).1 * (e y).1 = (e y).1 * (e x).1
      exact hMcomm _ _
    · change (e x).2 * (e y).2 = (e y).2 * (e x).2
      exact mul_comm' _ _
  have habel (x : F ≃ₐ[ℚ] F) (hx : x ∈ H)
      (y : F ≃ₐ[ℚ] F) (hy : y ∈ H) : x * y = y * x := by
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    simpa only [map_mul] using congrArg ι (hFcomm x' y')
  have hg : ι gF ∈ H := ⟨gF, rfl⟩
  have hdiff : c * gF.restrictScalars ℚ * c⁻¹ ≠ gF.restrictScalars ℚ := hθne
  have hc : c ∉ H := by
    intro hc
    have hcomm := habel c hc (ι gF) hg
    apply hdiff
    calc
      c * gF.restrictScalars ℚ * c⁻¹ =
          gF.restrictScalars ℚ * c * c⁻¹ := by
            change c * ι gF * c⁻¹ = ι gF * c * c⁻¹
            rw [hcomm]
      _ = gF.restrictScalars ℚ := by simp
  let nH : H.Normal := H.normal_of_index_eq_two hindex
  have hcg : c * ι gF * c⁻¹ ∈ H := nH.conj_mem (ι gF) hg c
  have hfix (x : F ≃ₐ[ℚ] F) (hx : x ∈ H) :
      x * ι gF * x⁻¹ = ι gF := by
    have hcomm := habel x hx (ι gF) hg
    calc
      x * ι gF * x⁻¹ = ι gF * x * x⁻¹ := by rw [hcomm]
      _ = ι gF := by simp [mul_assoc]
  have htwist (x : F ≃ₐ[ℚ] F) (hx : x ∉ H) :
      x * ι gF * x⁻¹ = c * ι gF * c⁻¹ := by
    have hcinv : c⁻¹ ∉ H := by simpa using hc
    have hu : x * c⁻¹ ∈ H := by
      rw [H.mul_mem_iff_of_index_two hindex]
      simp [hx, hcinv]
    let u := x * c⁻¹
    have hxu : x = u * c := by simp [u, mul_assoc]
    have hcomm := habel u hu (c * ι gF * c⁻¹) hcg
    calc
      x * ι gF * x⁻¹ = u * (c * ι gF * c⁻¹) * u⁻¹ := by rw [hxu]; group
      _ = c * ι gF * c⁻¹ := by rw [hcomm]; group
  have hclass : conjugatesOf (ι gF) = {ι gF, c * ι gF * c⁻¹} := by
    ext y
    rw [conjugatesOf, Set.mem_setOf_eq, isConj_iff]
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hx : x ∈ H
      · simp [hfix x hx]
      · simp [htwist x hx]
    · intro hy
      rcases (Set.mem_insert_iff.mp hy) with h | h
      · subst y
        exact ⟨1, by simp⟩
      · have h' : y = c * ι gF * c⁻¹ := Set.mem_singleton_iff.mp h
        subst y
        exact ⟨c, rfl⟩
  have hcount : (conjugatesOf (ι gF)).encard = 2 := by
    rw [hclass]
    have hdiff' : ι gF ≠ c * ι gF * c⁻¹ := hdiff.symm
    exact Set.encard_pair hdiff'
  have hCtot : Module.finrank ℚ C = Nat.totient (modulus j) :=
    IsCyclotomicExtension.Rat.finrank (modulus j) C
  have hCdegree : 2 * Module.finrank E C = Nat.totient (modulus j) := by
    calc
      2 * Module.finrank E C = Module.finrank ℚ E * Module.finrank E C := by
        rw [hE2]
      _ = Module.finrank ℚ C := Module.finrank_mul_finrank ℚ E C
      _ = Nat.totient (modulus j) := hCtot
  have hgroupcard : Nat.card (F ≃ₐ[ℚ] F) =
      Nat.totient (modulus j) *
        3 ^ (2 * (D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.support j).card + 2) := by
    calc
      Nat.card (F ≃ₐ[ℚ] F) = Module.finrank ℚ F :=
        IsGalois.card_aut_eq_finrank ℚ F
      _ = Module.finrank ℚ E * Module.finrank E F :=
        (Module.finrank_mul_finrank ℚ E F).symm
      _ = 2 * (3 ^ (2 * (D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.support j).card + 2) * Module.finrank E C) := by
        rw [hE2, hdegF]
      _ = (2 * Module.finrank E C) *
            3 ^ (2 * (D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.support j).card + 2) := by
        ring
      _ = Nat.totient (modulus j) *
            3 ^ (2 * (D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.support j).card + 2) := by
        rw [hCdegree]
  have hclasscard : Nat.card (ConjClasses.mk gQ).carrier = 2 := by
    change Nat.card (conjugatesOf (ι gF)) = 2
    rw [hclass, Nat.card_coe_set_eq]
    have hdiff' : ι gF ≠ c * ι gF * c⁻¹ := hθne.symm
    exact Set.ncard_pair hdiff'
  exact ⟨ζ, hζ, π, root, hdata, hEuler, hactualDisj, hFnormal,
    gcoord, hcoord, e, gM, σa, gF, heG, hgM, hσa,
    hpointM, hpointC, hdegF, hNF, hGal, hgfβ, hCcyclo, hres,
    c, τ, hτne, hcaction, hθβ, hθne, hclass, hcount,
    hclasscard, hgroupcard⟩
