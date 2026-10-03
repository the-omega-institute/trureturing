/- GID: D5/S3/Factorization/Galois/GoldenCubicCompatibilityDensity
   generality: I
   mirror-B: D5/B/S3/Factorization/Galois/GoldenCubicCompatibilityDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual GCC4 unrestricted rational primes have positive Dirichlet density and a compatible residue class. -/
import D5.S3.Factorization.Galois.GoldenCubicCompatibilityPrimeTransfer
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

private def rationalPrimeZetaSum (S : Set Nat.Primes) (s : ℝ) : ℝ :=
  ∑' p : S, ((p.1.1 : ℕ) : ℝ) ^ (-s)

def HasRationalPrimeDirichletDensity (S : Set Nat.Primes) (δ : ℝ) : Prop :=
  Filter.Tendsto
    (fun s : ℝ ↦ rationalPrimeZetaSum S s /
      rationalPrimeZetaSum Set.univ s)
    (𝓝[>] 1) (𝓝 δ)

def ActualDensityData (j : ℕ) (a : (ZMod (modulus j))ˣ) : Prop :=
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
                  qE.LiesOver (fp p)) ∧
                let δ : ℝ := (2 : ℝ) /
                  (Nat.totient (modulus j) * 3 ^ (2 * (support j).card + 2))
                HasRationalPrimeDirichletDensity T δ ∧ 0 < δ ∧
                (∃ b : (ZMod (modulus j))ˣ,
                  0 < b.val.val ∧ Odd (b.val.val % 16) ∧
                  ZMod.unitsMap (show 3 ∣ modulus j by
                    refine ⟨80 * 3 ^ (j + 1), ?_⟩
                    simp [modulus, pow_succ, mul_assoc, mul_comm]) b = 1 ∧
                  jacobiSym 5 b.val.val = 1 ∧
                  Int.ModEq (6 * (3 ^ (j + 1) : ℕ)) (b.val.val : ℤ)
                    (1 + 2 * (-1 : ℤ) ^ j * (3 ^ (j + 1) : ℕ)))

theorem actual_compatibility_density (j : ℕ) (a : (ZMod (modulus j))ˣ)
    (ha : ZMod.unitsMap (show 3 ∣ modulus j by
      refine ⟨80 * 3 ^ (j + 1), ?_⟩
      simp [modulus, pow_succ, mul_assoc, mul_comm]) a = 1) :
    ActualDensityData j a := by
  classical
  have hcomp := actual_compositum_data j a ha
  have hconj := actual_conjugacy_data j a ha hcomp
  have htransfer := actual_prime_transfer_data j a ha hconj
  letI : IsCyclotomicExtension {3} ℚ E :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  letI : IsGalois ℚ E := IsCyclotomicExtension.isGalois {3} ℚ E
  have hdiv : 3 ∣ modulus j := by
    refine ⟨80 * 3 ^ (j + 1), ?_⟩
    simp [modulus, pow_succ, mul_assoc, mul_comm]
  have ha' : ZMod.unitsMap hdiv a = 1 := ha
  dsimp only [ActualPrimeTransferData] at htransfer
  obtain ⟨ζ, hζ, π, root, hdata, hEuler, hactualDisj, hFnormal,
    gcoord, hcoord, e, gM, σa, gF, heG, hgM, hσa,
    hpointM, hpointC, hdegF, hNF, hGal, hgfβ, hCcyclo, hres,
    c, τ, hτne, hcaction, hθβ, hθne, hclass, hcount,
    hclasscard, hgroupcard, hGalM, hFiniteM, hgood_eq, hnorm, hprime,
    hnonzero, hinj, hsurj, hQover⟩ := htransfer
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
  have hZetaUnion : ∀ {S T : Set (Ideal (𝓞 ℚ))}, Disjoint S T → ∀ {s : ℝ}, 1 < s →
      Chebotarev.primeIdealZetaSum (S ∪ T) s = Chebotarev.primeIdealZetaSum S s + Chebotarev.primeIdealZetaSum T s := by
    intro S T hDisj s hs
    let eS : {𝔭 : Ideal (𝓞 ℚ) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
        ↑{x : {𝔭 : Ideal (𝓞 ℚ) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} | (x.1 : Ideal (𝓞 ℚ)) ∈ S} :=
      { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, Or.inl 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩, 𝔭.2.1⟩
        invFun := fun x ↦ ⟨x.1.1, x.2, x.1.2.2.1, x.1.2.2.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    let eT : {𝔭 : Ideal (𝓞 ℚ) // 𝔭 ∈ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
        ↑{x : {𝔭 : Ideal (𝓞 ℚ) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} | (x.1 : Ideal (𝓞 ℚ)) ∈ S}ᶜ :=
      { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, Or.inr 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩,
          fun h ↦ hDisj.le_bot ⟨h, 𝔭.2.1⟩⟩
        invFun := fun x ↦ ⟨x.1.1, x.1.2.1.resolve_left x.2, x.1.2.2.1, x.1.2.2.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [Chebotarev.primeIdealZetaSum, Chebotarev.primeIdealZetaSum,
      Chebotarev.primeIdealZetaSum,
      ← (show Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 ℚ) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from
      ((show Summable (fun I : NonzeroIdeal ℚ ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s)) from
        (((show HasSum (fun I : NonzeroIdeal ℚ ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))) (NumberField.dedekindZeta ℚ (s : ℂ)) from by
          have hcondition : 1 < ((s : ℂ)).re := (by simpa using hs)
          classical
          haveI (n : ℕ) : Finite {I : NonzeroIdeal ℚ // Ideal.absNorm I.1 = n} :=
            Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal ℚ ↦ I.1)
              ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 ℚ) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
              (fun _ _ _ _ ↦ Subtype.ext)
          have hseries : Summable fun n : ℕ ↦ ‖(idealNormMultiplicity ℚ n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ := by
            classical
            have hbig : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity ℚ k : ℝ))
                =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
              classical
              have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal ℚ | Ideal.absNorm I.1 = b}.Finite := fun b ↦
                Set.Finite.preimage (f := fun I : NonzeroIdeal ℚ ↦ I.1) (fun _ _ _ _ ↦ Subtype.ext)
                  (Ideal.finite_setOf_absNorm_eq (S := 𝓞 ℚ) b)
              have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity ℚ k =
                  Nat.card {I : NonzeroIdeal ℚ // Ideal.absNorm I.1 ≤ n} := fun n ↦ by
                have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal ℚ ↦
                  Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ ↦ h_finite b)
                rw [show ((fun I : NonzeroIdeal ℚ ↦ Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
                    {I : NonzeroIdeal ℚ | Ideal.absNorm I.1 ≤ n} by
                  ext ⟨I, hI⟩
                  simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_setOf_eq]
                  exact ⟨fun h ↦ h.2, fun h ↦
                    ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
                exact key.symm
              have h_card_bridge : ∀ n : ℕ,
                  Nat.card {I : NonzeroIdeal ℚ // Ideal.absNorm I.1 ≤ n} =
                  Nat.card {I : (Ideal (𝓞 ℚ))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
                fun n ↦ Nat.card_congr
                  { toFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                      ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
                    invFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                      ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
                    left_inv := fun _ ↦ rfl
                    right_inv := fun _ ↦ rfl }
              refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
                (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ ℚ).comp
                  tendsto_natCast_atTop_atTop).congr' ?_)
              filter_upwards with n
              simp only [Function.comp_apply, Real.rpow_one]
              rw [← Nat.cast_sum, h_sum_card n, h_card_bridge n]
              push_cast
              rfl
            have h_lss : LSeriesSummable (fun n : ℕ ↦ ((idealNormMultiplicity ℚ n : ℝ) : ℂ)) s :=
              LSeriesSummable_of_sum_norm_bigO_and_nonneg
                (f := fun n ↦ (idealNormMultiplicity ℚ n : ℝ))
                hbig (fun _ ↦ Nat.cast_nonneg _) zero_le_one
                (by exact_mod_cast hcondition)
            have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity ℚ n : ℝ) : ℂ)) (s : ℂ) =
                fun n ↦ (idealNormMultiplicity ℚ n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
              funext n
              simp only [LSeries.term]
              split_ifs with hn
              · subst hn
                have hzero : idealNormMultiplicity ℚ 0 = 0 := by
                    unfold idealNormMultiplicity
                    rw [Nat.card_eq_zero]
                    exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
                simp [hzero]
              · simp [Complex.cpow_neg, div_eq_mul_inv]
            exact (h_term_eq ▸ h_lss :
              Summable fun n ↦ (idealNormMultiplicity ℚ n : ℂ) * (n : ℂ) ^ (-(s : ℂ))).norm
          have hzeta : NumberField.dedekindZeta ℚ (s : ℂ) =
              ∑' n : ℕ, (idealNormMultiplicity ℚ n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
            unfold NumberField.dedekindZeta LSeries
            refine tsum_congr fun n ↦ ?_
            unfold LSeries.term
            rcases Nat.eq_zero_or_pos n with rfl | hn
            · have hs0 : (s : ℂ) ≠ 0 := by
                intro hzero
                have hre := congrArg Complex.re hzero
                simp only [Complex.zero_re] at hre
                rw [hre] at hcondition
                norm_num at hcondition
              have hzero : idealNormMultiplicity ℚ 0 = 0 := by
                  unfold idealNormMultiplicity
                  rw [Nat.card_eq_zero]
                  exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
              simp [hzero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
            · simp only [hn.ne', ↓reduceIte]
              rw [Complex.cpow_neg, div_eq_mul_inv]
              congr 1
              unfold idealNormMultiplicity
              have hequiv : {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} ≃
                  {I : NonzeroIdeal ℚ // Ideal.absNorm I.1 = n} := by
                refine {
                  toFun := fun ⟨I, hI⟩ ↦ ⟨⟨I, ?_⟩, hI⟩
                  invFun := fun ⟨⟨I, _⟩, hI⟩ ↦ ⟨I, hI⟩
                  left_inv := fun _ ↦ rfl
                  right_inv := fun _ ↦ rfl }
                intro h
                rw [h, Ideal.absNorm_bot] at hI
                lia
              exact_mod_cast Nat.card_congr hequiv
          set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal ℚ ↦ Ideal.absNorm I.1)
          have hval : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal ℚ // Ideal.absNorm I.1 = n},
              (Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))) = (idealNormMultiplicity ℚ n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) :=
            fun n ↦ by
              rw [show (∑' y : {I : NonzeroIdeal ℚ // Ideal.absNorm I.1 = n},
                  (Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))) = idealNormMultiplicity ℚ n • (n : ℂ) ^ (-(s : ℂ)) from
                (tsum_congr fun y : {I : NonzeroIdeal ℚ // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
                  (tsum_const ((n : ℂ) ^ (-(s : ℂ)))), nsmul_eq_mul]
          have hnorm : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal ℚ // Ideal.absNorm I.1 = n},
              ‖(Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))‖) = ‖(idealNormMultiplicity ℚ n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ :=
            fun n ↦ by
              rw [show (∑' y : {I : NonzeroIdeal ℚ // Ideal.absNorm I.1 = n},
                  ‖(Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))‖) = idealNormMultiplicity ℚ n • ‖(n : ℂ) ^ (-(s : ℂ))‖ from
                (tsum_congr fun y : {I : NonzeroIdeal ℚ // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
                  (tsum_const ‖(n : ℂ) ^ (-(s : ℂ))‖), nsmul_eq_mul, norm_mul,
                Complex.norm_natCast]
          have hsummable : Summable fun I : NonzeroIdeal ℚ ↦ ‖(Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))‖ := by
            rw [← e.summable_iff]
            refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun _ ↦ Summable.of_finite, ?_⟩
            exact hseries.congr fun n ↦ (hnorm n).symm
          have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal ℚ // Ideal.absNorm I.1 = n} ↦
              (Ideal.absNorm (e p).1 : ℂ) ^ (-(s : ℂ)) :=
            (e.summable_iff (f := fun I : NonzeroIdeal ℚ ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))).mpr
              hsummable.of_norm
          have hval_sum : (∑' I : NonzeroIdeal ℚ, (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))
              = NumberField.dedekindZeta ℚ s := by
            rw [hzeta,
              ← e.tsum_eq (fun I ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))), hsummable_sigma.tsum_sigma]
            exact tsum_congr hval
          exact hval_sum ▸ hsummable.of_norm.hasSum)).summable.norm).congr
          fun I ↦ (Complex.norm_natCast_cpow_of_pos
            (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2)) _).trans <| by simp)).comp_injective
        (i := fun 𝔭 : {𝔭 : Ideal (𝓞 ℚ) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
          (⟨𝔭.1, 𝔭.2.2.2⟩ : NonzeroIdeal ℚ))
        (fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab))).tsum_subtype_add_tsum_subtype_compl
        {x | (x.1 : Ideal (𝓞 ℚ)) ∈ S},
      ← eS.tsum_eq (fun x ↦ (Ideal.absNorm (x.1 : Ideal (𝓞 ℚ)) : ℝ) ^ (-s)),
      ← eT.tsum_eq (fun x ↦ (Ideal.absNorm (x.1 : Ideal (𝓞 ℚ)) : ℝ) ^ (-s))]
    rfl 
  have hcheb := Chebotarev.chebotarev_density (K := ℚ) (L := F) (ConjClasses.mk gQ)
  have hclasscard' : Nat.card (ConjClasses.mk gQ).carrier = 2 := hclasscard
  have hgroupcard' : Nat.card (F ≃ₐ[ℚ] F) = Nat.totient (modulus j) *
      3 ^ (2 * (support j).card + 2) := hgroupcard
  have hdensity : Chebotarev.HasDirichletDensity
      {𝔭 : Ideal (𝓞 ℚ) | 𝔭.IsPrime ∧ Chebotarev.UnramifiedIn ℚ F 𝔭 ∧
        Chebotarev.frobeniusClass ℚ F 𝔭 = ConjClasses.mk gQ}
      ((2 : ℝ) / (Nat.totient (modulus j) *
        3 ^ (2 * (D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.support j).card + 2))) := by
    simpa only [hclasscard', hgroupcard', Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      using hcheb
  let S : Set (Ideal (𝓞 ℚ)) :=
    {𝔭 | 𝔭.IsPrime ∧ Chebotarev.UnramifiedIn ℚ F 𝔭 ∧
      Chebotarev.frobeniusClass ℚ F 𝔭 = ConjClasses.mk gQ}
  let B : Set (Ideal (𝓞 ℚ)) :=
    {𝔭 | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ (Ideal.absNorm 𝔭).Coprime (modulus j)}
  have hbad : B.Finite := by
    classical
    refine Set.Finite.subset
      (Set.Finite.biUnion (s := (↑(modulus j).primeFactors : Set ℕ))
        (t := fun p : ℕ =>
          {𝔭 : Ideal (𝓞 ℚ) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ (p : 𝓞 ℚ) ∈ 𝔭})
        (Set.toFinite _) fun p hp ↦ ?_)
      ?_
    · have hp0 : p ≠ 0 := (Nat.pos_of_mem_primeFactors hp).ne'
      have hspan : (Ideal.span {(p : 𝓞 ℚ)}) ≠ 0 := by
        simp only [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
        exact_mod_cast hp0
      refine ((Ideal.finite_factors (R := 𝓞 ℚ) hspan).image (·.asIdeal)).subset ?_
      rintro 𝔭 ⟨hprime, hne, hmem⟩
      exact ⟨⟨𝔭, hprime, hne⟩,
        Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem), rfl⟩
    · rintro 𝔭 ⟨hprime, hne, hncop⟩
      have := hprime
      have hfactor : ∃ p ∈ (modulus j).primeFactors, (p : 𝓞 ℚ) ∈ 𝔭 := by
        have h𝔭 : 𝔭 ≠ ⊥ := hne
        have hN0 : Ideal.absNorm 𝔭 ≠ 0 :=
          fun h ↦ h𝔭 (Ideal.absNorm_eq_zero_iff.mp h)
        have hN1' : Ideal.absNorm 𝔭 ≠ 1 :=
          fun h ↦ ‹𝔭.IsPrime›.ne_top (Ideal.absNorm_eq_one_iff.mp h)
        obtain ⟨r, hr, hrdvd, hrm⟩ :=
          exists_prime_dvd_natCast_mem ℚ 𝔭 _ (by lia) (Ideal.absNorm_mem 𝔭)
        have hNdvd : Ideal.absNorm 𝔭 ∣ r ^ Module.finrank ℤ (𝓞 ℚ) := by
          have hd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hrm)
          rw [Ideal.absNorm_span_singleton,
            show ((r : ℕ) : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (r : ℤ) by
              push_cast
              rfl,
            Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at hd
          exact hd
        obtain ⟨p, hp, hpdvd⟩ :=
          Nat.exists_prime_and_dvd (hncop : Nat.gcd (Ideal.absNorm 𝔭) (modulus j) ≠ 1)
        have hpr : p ∣ r ^ Module.finrank ℤ (𝓞 ℚ) :=
          (hpdvd.trans (Nat.gcd_dvd_left _ _)).trans hNdvd
        have hpeqr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpr)
        exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans (Nat.gcd_dvd_right _ _), NeZero.ne (modulus j)⟩,
          hpeqr ▸ hrm⟩
      obtain ⟨p, hp, hpmem⟩ := hfactor
      exact Set.mem_biUnion hp ⟨hprime, hne, hpmem⟩
  have heq : S \ B =
      {𝔭 : Ideal (𝓞 ℚ) | 𝔭.IsPrime ∧ Chebotarev.UnramifiedIn ℚ F 𝔭 ∧
        Chebotarev.frobeniusClass ℚ F 𝔭 = ConjClasses.mk gQ ∧
        (Ideal.absNorm 𝔭).Coprime (modulus j)} := by
    ext 𝔭
    constructor
    · rintro ⟨⟨hp, hunr, hclass⟩, hnotbad⟩
      refine ⟨hp, hunr, hclass, ?_⟩
      by_contra hn
      exact hnotbad ⟨hp, hunr.1, hn⟩
    · rintro ⟨hp, hunr, hclass, hcop⟩
      exact ⟨⟨hp, hunr, hclass⟩, fun hbad => hbad.2.2 hcop⟩
  have hSB : (S ∩ B).Finite := hbad.subset (by intro x hx; exact hx.2)
  have hSBdens : Chebotarev.HasDirichletDensity (S ∩ B) 0 :=
    Chebotarev.hasDirichletDensity_of_finite ℚ hSB
  have hdecomp : S = (S \ B) ∪ (S ∩ B) := by
    ext x
    simp only [Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
    tauto
  have hdisj : Disjoint (S \ B) (S ∩ B) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact hx.2 hy.2
  have hgooddensity : Chebotarev.HasDirichletDensity
      {𝔭 : Ideal (𝓞 ℚ) | 𝔭.IsPrime ∧ Chebotarev.UnramifiedIn ℚ F 𝔭 ∧
        Chebotarev.frobeniusClass ℚ F 𝔭 = ConjClasses.mk gQ ∧
        (Ideal.absNorm 𝔭).Coprime (modulus j)}
      ((2 : ℝ) / (Nat.totient (modulus j) *
        3 ^ (2 * (D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.support j).card + 2))) := by
    rw [← heq]
    unfold Chebotarev.HasDirichletDensity at hdensity hSBdens ⊢
    have hlimit := hdensity.sub hSBdens
    have hevent : ∀ᶠ s in 𝓝[>] (1 : ℝ),
        Chebotarev.primeIdealZetaSum (S \ B) s /
            Chebotarev.primeIdealZetaSum (univ : Set (Ideal (𝓞 ℚ))) s =
          Chebotarev.primeIdealZetaSum S s /
              Chebotarev.primeIdealZetaSum (univ : Set (Ideal (𝓞 ℚ))) s -
          Chebotarev.primeIdealZetaSum (S ∩ B) s /
              Chebotarev.primeIdealZetaSum (univ : Set (Ideal (𝓞 ℚ))) s := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hsum : Chebotarev.primeIdealZetaSum S s =
          Chebotarev.primeIdealZetaSum (S \ B) s +
            Chebotarev.primeIdealZetaSum (S ∩ B) s := by
        calc
          Chebotarev.primeIdealZetaSum S s =
              Chebotarev.primeIdealZetaSum ((S \ B) ∪ (S ∩ B)) s :=
                congrArg (fun T => Chebotarev.primeIdealZetaSum T s) hdecomp
          _ = Chebotarev.primeIdealZetaSum (S \ B) s +
              Chebotarev.primeIdealZetaSum (S ∩ B) s :=
            (hZetaUnion hdisj hs)
      rw [hsum]
      ring
    simpa only [sub_zero] using
      hlimit.congr' (hevent.mono (fun s hs => hs.symm))
  have hdensitypos : 0 < ((2 : ℝ) / (Nat.totient (modulus j) *
      3 ^ (2 * (D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.support j).card + 2))) := by
    have hmpos : 0 < modulus j := by
      dsimp [modulus]
      positivity
    have htot : 0 < Nat.totient (modulus j) := Nat.totient_pos.mpr hmpos
    have hdenNat : 0 < Nat.totient (modulus j) *
        3 ^ (2 * (D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.support j).card + 2) :=
      Nat.mul_pos htot (pow_pos (by norm_num) _)
    have hden : (0 : ℝ) < (Nat.totient (modulus j) *
        3 ^ (2 * (D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.support j).card + 2) : ℕ) := by
      exact_mod_cast hdenNat
    exact div_pos (by norm_num) (by
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hden)
  let δ : ℝ := (2 : ℝ) / (Nat.totient (modulus j) *
    3 ^ (2 * (D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.support j).card + 2))
  have hRfin : R.Finite := by
    let : Algebra (FractionRing (𝓞 ℚ)) (FractionRing (𝓞 F)) :=
      FractionRing.liftAlgebra (𝓞 ℚ) (FractionRing (𝓞 F))
    have hbot : differentIdeal (𝓞 ℚ) (𝓞 F) ≠ 0 := by
      rw [Ideal.zero_eq_bot]
      exact differentIdeal_ne_bot
    apply Set.Finite.subset
      ((Ideal.finite_factors hbot).image (fun v ↦ (v.asIdeal).under (𝓞 ℚ)))
    rintro 𝔭 ⟨-, h𝔭bot, hnunr⟩
    simp only [UnramifiedIn, not_and, not_forall] at hnunr
    obtain ⟨𝔓, h𝔓max, h𝔓lo, h𝔓nu⟩ := hnunr h𝔭bot
    have := h𝔓max.isPrime
    have := h𝔓lo
    have h𝔓bot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭bot 𝔓
    have hdvd : 𝔓 ∣ differentIdeal (𝓞 ℚ) (𝓞 F) := by
      by_contra h
      exact h𝔓nu (not_dvd_differentIdeal_iff.mp h)
    exact ⟨⟨𝔓, h𝔓max.isPrime, h𝔓bot⟩, hdvd, h𝔓lo.over.symm⟩
  have hSdens : Chebotarev.HasDirichletDensity (U \ R) δ := by
    rw [← hgood_eq]
    exact hgooddensity
  have hURfin : (U ∩ R).Finite :=
    hRfin.subset (by intro q hq; exact hq.2)
  have hURzero : Chebotarev.HasDirichletDensity (U ∩ R) 0 :=
    Chebotarev.hasDirichletDensity_of_finite ℚ hURfin
  have hdisj : Disjoint (U \ R) (U ∩ R) := by
    rw [Set.disjoint_left]
    intro q hq hq'
    exact hq.2 hq'.2
  have hdecomp : U = (U \ R) ∪ (U ∩ R) := by
    ext q
    simp only [Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
    tauto
  have hUdens : Chebotarev.HasDirichletDensity U δ := by
    unfold Chebotarev.HasDirichletDensity at hSdens hURzero ⊢
    have hlimit := hSdens.add hURzero
    have hevent : ∀ᶠ s in 𝓝[>] (1 : ℝ),
        Chebotarev.primeIdealZetaSum U s /
            Chebotarev.primeIdealZetaSum (univ : Set (Ideal (𝓞 ℚ))) s =
          Chebotarev.primeIdealZetaSum (U \ R) s /
              Chebotarev.primeIdealZetaSum (univ : Set (Ideal (𝓞 ℚ))) s +
          Chebotarev.primeIdealZetaSum (U ∩ R) s /
              Chebotarev.primeIdealZetaSum (univ : Set (Ideal (𝓞 ℚ))) s := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hsum : Chebotarev.primeIdealZetaSum U s =
          Chebotarev.primeIdealZetaSum (U \ R) s +
            Chebotarev.primeIdealZetaSum (U ∩ R) s := by
        calc
          Chebotarev.primeIdealZetaSum U s =
              Chebotarev.primeIdealZetaSum ((U \ R) ∪ (U ∩ R)) s :=
                congrArg (fun T => Chebotarev.primeIdealZetaSum T s) hdecomp
          _ = _ := hZetaUnion hdisj hs
      rw [hsum, add_div]
    simpa only [add_zero] using hlimit.congr' (hevent.mono (fun s hs => hs.symm))
  let R_M : Set (Ideal (𝓞 E)) :=
    {qE | qE.IsPrime ∧ qE ≠ ⊥ ∧ ¬ Chebotarev.UnramifiedIn E M qE}
  let R_Q : Set (Ideal (𝓞 ℚ)) :=
    (fun qE : Ideal (𝓞 E) => qE.under (𝓞 ℚ)) '' R_M
  have hRMfin : R_M.Finite := by
    let : Algebra (FractionRing (𝓞 E)) (FractionRing (𝓞 M)) :=
      FractionRing.liftAlgebra (𝓞 E) (FractionRing (𝓞 M))
    have : IsScalarTower (𝓞 E) (FractionRing (𝓞 E)) (FractionRing (𝓞 M)) :=
      FractionRing.isScalarTower_liftAlgebra (𝓞 E) (FractionRing (𝓞 M))
    have hbot : differentIdeal (𝓞 E) (𝓞 M) ≠ 0 := by
      rw [Ideal.zero_eq_bot]
      exact differentIdeal_ne_bot
    apply Set.Finite.subset
      ((Ideal.finite_factors hbot).image (fun v ↦ (v.asIdeal).under (𝓞 E)))
    rintro 𝔭 ⟨-, h𝔭bot, hnunr⟩
    simp only [UnramifiedIn, not_and, not_forall] at hnunr
    obtain ⟨𝔓, h𝔓max, h𝔓lo, h𝔓nu⟩ := hnunr h𝔭bot
    have := h𝔓max.isPrime
    have := h𝔓lo
    have h𝔓bot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭bot 𝔓
    have hdvd : 𝔓 ∣ differentIdeal (𝓞 E) (𝓞 M) := by
      by_contra h
      exact h𝔓nu (not_dvd_differentIdeal_iff.mp h)
    exact ⟨⟨𝔓, h𝔓max.isPrime, h𝔓bot⟩, hdvd, h𝔓lo.over.symm⟩
  have hRQfin : R_Q.Finite := hRMfin.image _
  let U_unr : Set (Ideal (𝓞 ℚ)) := fp '' T_unr
  have hTunrSub : T_unr ⊆ T := by
    intro p hp
    obtain ⟨hmod, qE, hqE, hoverE, _, qM, hqM, hoverM, hM⟩ := hp
    exact ⟨hmod, qE, hqE, hoverE, qM, hqM, hoverM, hM⟩
  have hUunrSub : U_unr ⊆ U := Set.image_mono hTunrSub
  have hUdiffFin : (U \ U_unr).Finite := by
    apply hRQfin.subset
    intro q hq
    obtain ⟨p, hpT, rfl⟩ := hq.1
    have hpnot : p ∉ T_unr := by
      intro hpU
      exact hq.2 ⟨p, hpU, rfl⟩
    obtain ⟨hmod, qE, hqE, hoverE, qM, hqM, hoverM, hM⟩ := hpT
    have hram : ¬ Chebotarev.UnramifiedIn E M qE := by
      intro hunrE
      exact hpnot ⟨hmod, qE, hqE, hoverE, hunrE,
        qM, hqM, hoverM, hM⟩
    have hqover : qE.LiesOver (fp p) := hQover p qE hoverE
    have hqEne : qE ≠ ⊥ :=
      Ideal.ne_bot_of_liesOver_of_ne_bot (hnonzero p) qE
    exact ⟨qE, ⟨hqE, hqEne, hram⟩, hqover.over.symm⟩
  have hUdiffZero : Chebotarev.HasDirichletDensity (U \ U_unr) 0 :=
    Chebotarev.hasDirichletDensity_of_finite ℚ hUdiffFin
  have hUunrDisj : Disjoint U_unr (U \ U_unr) := by
    rw [Set.disjoint_left]
    intro q hq hq'
    exact hq'.2 hq
  have hUunrDecomp : U = U_unr ∪ (U \ U_unr) := by
    ext q
    simp only [Set.mem_union, Set.mem_diff]
    constructor
    · intro hq
      by_cases hqU : q ∈ U_unr
      · exact Or.inl hqU
      · exact Or.inr ⟨hq, hqU⟩
    · rintro (hq | ⟨hq, _⟩)
      · exact hUunrSub hq
      · exact hq
  have hUunrDensity : Chebotarev.HasDirichletDensity U_unr δ := by
    unfold Chebotarev.HasDirichletDensity at hUdens hUdiffZero ⊢
    have hlimit := hUdens.sub hUdiffZero
    have hevent : ∀ᶠ s in 𝓝[>] (1 : ℝ),
        Chebotarev.primeIdealZetaSum U_unr s /
            Chebotarev.primeIdealZetaSum
              (Set.univ : Set (Ideal (𝓞 ℚ))) s =
          Chebotarev.primeIdealZetaSum U s /
              Chebotarev.primeIdealZetaSum
                (Set.univ : Set (Ideal (𝓞 ℚ))) s -
          Chebotarev.primeIdealZetaSum (U \ U_unr) s /
              Chebotarev.primeIdealZetaSum
                (Set.univ : Set (Ideal (𝓞 ℚ))) s := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hsumU : Chebotarev.primeIdealZetaSum U s =
          Chebotarev.primeIdealZetaSum U_unr s +
            Chebotarev.primeIdealZetaSum (U \ U_unr) s := by
        calc
          Chebotarev.primeIdealZetaSum U s =
              Chebotarev.primeIdealZetaSum
                (U_unr ∪ (U \ U_unr)) s :=
              congrArg (fun V => Chebotarev.primeIdealZetaSum V s)
                hUunrDecomp
          _ = Chebotarev.primeIdealZetaSum U_unr s +
              Chebotarev.primeIdealZetaSum (U \ U_unr) s :=
            (hZetaUnion hUunrDisj hs)
      rw [hsumU]
      ring
    simpa only [sub_zero] using
      hlimit.congr' (hevent.mono (fun s hs => hs.symm))
  let primeEquiv : Nat.Primes ≃
      {I : Ideal (𝓞 ℚ) // I.IsPrime ∧ I ≠ ⊥} :=
    Equiv.ofBijective
      (fun p => ⟨fp p, hprime p, hnonzero p⟩) ⟨
        (fun p q hpq => hinj (congrArg Subtype.val hpq)),
        (fun I => by
          obtain ⟨p, hp⟩ := hsurj I.1 I.2.1 I.2.2
          exact ⟨p, Subtype.ext hp⟩)⟩
  have hsum (V : Set Nat.Primes) (s : ℝ) :
      Chebotarev.primeIdealZetaSum (fp '' V) s =
        rationalPrimeZetaSum V s := by
    have hmem (p : Nat.Primes) : p ∈ V ↔ (primeEquiv p).1 ∈ fp '' V := by
      change p ∈ V ↔ fp p ∈ fp '' V
      constructor
      · intro hp; exact ⟨p, hp, rfl⟩
      · rintro ⟨q, hq, hqp⟩
        exact (hinj hqp).symm ▸ hq
    let eV : V ≃
        {I : Ideal (𝓞 ℚ) // I ∈ fp '' V ∧ I.IsPrime ∧ I ≠ ⊥} :=
      (primeEquiv.subtypeEquiv hmem).trans <|
        (Equiv.subtypeSubtypeEquivSubtypeInter
          (fun I : Ideal (𝓞 ℚ) => I.IsPrime ∧ I ≠ ⊥)
          (fun I => I ∈ fp '' V)).trans <|
          Equiv.subtypeEquivRight (fun _ => by tauto)
    unfold Chebotarev.primeIdealZetaSum rationalPrimeZetaSum
    rw [← eV.tsum_eq (fun I => (Ideal.absNorm I.1 : ℝ) ^ (-s))]
    congr 1
    funext p
    change (Ideal.absNorm (fp p.1) : ℝ) ^ (-s) =
      ((p.1.1 : ℕ) : ℝ) ^ (-s)
    rw [hnorm]
  have huniv (s : ℝ) :
      Chebotarev.primeIdealZetaSum
          (Set.univ : Set (Ideal (𝓞 ℚ))) s =
        rationalPrimeZetaSum Set.univ s := by
    have hAllSum : ∀ (S : Set (Ideal (𝓞 ℚ))),
              (∀ 𝔭 : Ideal (𝓞 ℚ), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭 ∈ S) → ∀ s : ℝ,
              Chebotarev.primeIdealZetaSum S s =
                Chebotarev.primeIdealZetaSum (univ : Set (Ideal (𝓞 ℚ))) s := by
            intro S hS s
            let e : {𝔭 : Ideal (𝓞 ℚ) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
                {𝔭 : Ideal (𝓞 ℚ) // 𝔭 ∈ (univ : Set (Ideal (𝓞 ℚ))) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
              Equiv.subtypeEquivRight fun 𝔭 ↦
                ⟨fun h ↦ ⟨mem_univ _, h.2⟩, fun h ↦ ⟨hS 𝔭 h.2.1 h.2.2, h.2⟩⟩
            rw [Chebotarev.primeIdealZetaSum, Chebotarev.primeIdealZetaSum,
              ← e.tsum_eq (fun 𝔭 ↦ (Ideal.absNorm (𝔭.1 : Ideal (𝓞 ℚ)) : ℝ) ^ (-s))]
            rfl
    rw [← hAllSum (fp '' (Set.univ : Set Nat.Primes)) (fun I hp hne => by
        obtain ⟨p, rfl⟩ := hsurj I hp hne
        exact ⟨p, Set.mem_univ _, rfl⟩) s]
    exact hsum Set.univ s
  have hNatural : HasRationalPrimeDirichletDensity T_unr δ := by
    change Filter.Tendsto
      (fun s : ℝ =>
        Chebotarev.primeIdealZetaSum (fp '' T_unr) s /
          Chebotarev.primeIdealZetaSum
            (Set.univ : Set (Ideal (𝓞 ℚ))) s)
      (𝓝[>] 1) (𝓝 δ) at hUunrDensity
    change Filter.Tendsto
      (fun s : ℝ => rationalPrimeZetaSum T_unr s /
        rationalPrimeZetaSum Set.univ s)
      (𝓝[>] 1) (𝓝 δ)
    simpa only [hsum, huniv] using hUunrDensity
  have hNaturalFull : HasRationalPrimeDirichletDensity T δ := by
    change Filter.Tendsto
      (fun s : ℝ =>
        Chebotarev.primeIdealZetaSum (fp '' T) s /
          Chebotarev.primeIdealZetaSum
            (Set.univ : Set (Ideal (𝓞 ℚ))) s)
      (𝓝[>] 1) (𝓝 δ) at hUdens
    change Filter.Tendsto
      (fun s : ℝ => rationalPrimeZetaSum T s /
        rationalPrimeZetaSum Set.univ s)
      (𝓝[>] 1) (𝓝 δ)
    simpa only [hsum, huniv] using hUdens
  have hCRT :
      ∃ b : (ZMod (modulus j))ˣ,
        0 < b.val.val ∧ Odd (b.val.val % 16) ∧
        ZMod.unitsMap (show 3 ∣ modulus j by
          refine ⟨80 * 3 ^ (j + 1), ?_⟩
          simp [modulus, pow_succ, mul_assoc, mul_comm]) b = 1 ∧
        jacobiSym 5 b.val.val = 1 ∧
        Int.ModEq (6 * (3 ^ (j + 1) : ℕ)) (b.val.val : ℤ)
          (1 + 2 * (-1 : ℤ) ^ j * (3 ^ (j + 1) : ℕ)) := by
    let r : ℕ := 3 ^ (j + 1)
    let n : ℕ := if Even j then 1 + 20 * r else 1 + 10 * r
    have hrpos : 0 < r := pow_pos (by decide) _
    have hr3 : 3 ∣ r := by
      refine ⟨3 ^ j, ?_⟩
      simp [r, pow_succ, mul_comm]
    have hm : modulus j = 240 * r := by
      simp only [modulus, r]
      rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
      ring
    have hnpos : 0 < n := by
      dsimp [n]
      split_ifs <;> omega
    have hnlt : n < modulus j := by
      rw [hm]
      dsimp [n]
      split_ifs <;> omega
    have hnmod2 : n % 2 = 1 := by
      dsimp [n]
      split_ifs <;> omega
    have hnmod3 : n % 3 = 1 := by
      dsimp [n]
      split_ifs <;> omega
    have hnmod5 : n % 5 = 1 := by
      dsimp [n]
      split_ifs <;> omega
    have hcop : n.Coprime (modulus j) := by
      have htwo : n.Coprime (2 ^ 4) :=
        (by norm_num : Nat.Prime 2).coprime_pow_of_not_dvd (by omega)
      have hfive : n.Coprime (5 ^ 1) :=
        (by norm_num : Nat.Prime 5).coprime_pow_of_not_dvd (by omega)
      have hthree : n.Coprime (3 ^ (j + 2)) :=
        (by norm_num : Nat.Prime 3).coprime_pow_of_not_dvd (by omega)
      have h := (htwo.mul_right hfive).mul_right hthree
      simpa [modulus] using h
    let a : (ZMod (modulus j))ˣ := ZMod.unitOfCoprime n hcop
    have hval : a.val.val = n := by
      simpa only [a, ZMod.coe_unitOfCoprime] using
        (ZMod.val_natCast_of_lt hnlt)
    have hodd16 : Odd (n % 16) := Nat.odd_iff.mpr (by omega)
    have hthree : (n : ZMod 3) = 1 := by
      have hrz : (r : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff r 3).mpr hr3
      dsimp [n]
      split_ifs <;> push_cast <;> simp [hrz]
    have hdiv3 : 3 ∣ modulus j := by
      refine ⟨80 * 3 ^ (j + 1), ?_⟩
      simp [modulus, pow_succ, mul_assoc, mul_comm]
    have ha : ZMod.unitsMap hdiv3 a = 1 := by
      apply Units.ext
      change ((a.val).cast : ZMod 3) = 1
      rw [show a.val = (n : ZMod (modulus j)) from
        ZMod.coe_unitOfCoprime n hcop]
      rw [ZMod.cast_natCast hdiv3 n]
      exact hthree
    have hjac : jacobiSym 5 n = 1 := by
      have hqr : jacobiSym 5 n = jacobiSym (n : ℤ) 5 := by
        simpa only [Nat.cast_ofNat] using
          (jacobiSym.quadratic_reciprocity_one_mod_four
            (a := 5) (b := n) (by decide) (Nat.odd_iff.mpr hnmod2))
      rw [hqr, jacobiSym.mod_left]
      have hi : ((n : ℤ) % 5) = 1 := by
        simpa only [Int.natCast_mod, Nat.cast_ofNat, Nat.cast_one] using congrArg (fun x : ℕ => (x : ℤ)) hnmod5
      simpa only [Nat.cast_ofNat, hi, jacobiSym.one_left]
    have hcrt : Int.ModEq (6 * (r : ℤ)) (n : ℤ)
        (1 + 2 * (-1 : ℤ) ^ j * (r : ℤ)) := by
      rw [Int.modEq_iff_dvd]
      by_cases hj : Even j
      · have hn : n = 1 + 20 * r := by simp only [n, if_pos hj]
        rw [hn, hj.neg_one_pow]
        refine ⟨-3, ?_⟩
        push_cast
        ring
      · have hodd : Odd j := Nat.not_even_iff_odd.mp hj
        have hn : n = 1 + 10 * r := by simp only [n, if_neg hj]
        rw [hn, hodd.neg_one_pow]
        refine ⟨-2, ?_⟩
        push_cast
        ring
    refine ⟨a, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hval]
      exact hnpos
    · rw [hval]
      exact hodd16
    · simpa only using ha
    · rw [hval]
      exact hjac
    · simpa only [hval, r] using hcrt
  exact ⟨ζ, hζ, π, root, hdata, hEuler, hactualDisj, hFnormal,
    gcoord, hcoord, e, gM, σa, gF, heG, hgM, hσa,
    hpointM, hpointC, hdegF, hNF, hGal, hgfβ, hCcyclo, hres,
    c, τ, hτne, hcaction, hθβ, hθne, hclass, hcount,
    hclasscard, hgroupcard, (inferInstance : IsGalois E M),
    (inferInstance : FiniteDimensional E M), hgood_eq, hnorm, hprime,
    hnonzero, hinj, hsurj, hQover, hNaturalFull, hdensitypos, hCRT⟩
