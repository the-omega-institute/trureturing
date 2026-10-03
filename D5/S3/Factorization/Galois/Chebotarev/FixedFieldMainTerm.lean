/- GID: D5/S3/Factorization/Galois/Chebotarev/FixedFieldMainTerm
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/Chebotarev/FixedFieldMainTerm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The degree-one fixed-field prime sum is a scalar multiple of the base Frobenius-fibre sum. -/
module

public import D5.S3.Factorization.Galois.Chebotarev.FixedFieldFrobeniusCounting

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import D5.S3.Factorization.Galois.Chebotarev.Cyclotomic

/-!
# Density transfer through a fixed-field subextension (Sharifi 7.2.2 Step 1)

The cyclic-reduction core of Chebotarev's density theorem. For `σ ∈ Gal(L/K)` and the
fixed field `E = L^⟨σ⟩` (so `L/E` is cyclic of degree `f = ord σ`), a counting argument
over the primes of `L` above a prime of `K` relates the Dirichlet density of the
`σ`-Frobenius fibre of `K` to that of the `σ_E`-Frobenius fibre of `E`:

  δ_K(S) = (f·|C|/|G|)·δ_E(T_σ).

The key result `density_lift_through_fixedField` packages this transfer: given the abelian
(cyclic) density `1/|Gal(L/E)|` of the `E`-fibre, it yields the `K`-fibre density
`|C|/|Gal(L/K)|`.

This is the Step-1 reduction of Sharifi 7.2.2 (p. 143), placed in its own module strictly
below both `Main.lean` (which consumes it for `chebotarev_density`) and `Abelian.lean`
(whose cyclotomic-crossing master leaf reuses it via the compositum `M/F`). The block is
independent of `chebotarev_abelian`: its only ingredients are the Frobenius/inertia counting
of `Frobenius.lean` and the Dirichlet-sum asymptotics of `Density.lean`/`ZetaProduct.lean`.

## Main results

* `Chebotarev.density_lift_through_fixedField` — the cyclic density transfer through `E/K`.

## References

* Sharifi, *Algebraic Number Theory*, Theorem 7.2.2 Step 1 (`docs/algnum.pdf`, p. 143).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*, Appendix (`docs/cheb.pdf`, p. 18).
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

open Filter NumberField Topology Set

open scoped ENNReal Pointwise

namespace Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]


/-- **The fixed-field Frobenius below `𝔓` is `σ_E`** (Sharifi 7.2.2 p. 143). For an L-prime
`𝔓` with `Frob^K_𝔓 = σ` lying over a degree-one (over `K`) prime `P = 𝔓 ∩ 𝓞 E`, the
`E`-Frobenius `Frob^E_𝔓` restricts to `σ`, hence (as `σ_E` also restricts to `σ` and
`restrictScalars` is injective) `Frob^E_𝔓 = σ_E`. -/
private theorem arithFrobAt_E_eq_of_isArithFrobAt
    (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hσE : letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      σE.restrictScalars K = σ)
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hunrK : UnramifiedIn K L (𝔓.under (𝓞 K)))
    (hPK : 𝔓.LiesOver (𝔓.under (𝓞 K)))
    (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓)
    (_horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hraE : Ideal.ramificationIdx'
        (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓 = 1)
    (hnorm : Nat.card (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))
          ⧸ 𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
        = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K))) :
    haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
      (Ideal.ne_bot_of_liesOver_of_ne_bot hunrK.1 𝔓)
    haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
      IsGalois.tower_top_intermediateField _
    arithFrobAt (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
      Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓 = σE := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
    IsGalois.tower_top_intermediateField _
  have hPbot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hunrK.1 𝔓
  have hraK : Ideal.ramificationIdx' (𝔓.under (𝓞 K)) 𝔓 = 1 := by
    have hpbot := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
    haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
      hunrK.2 𝔓 (‹𝔓.IsPrime›.isMaximal hPbot) hPK
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 hpbot]
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
  haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
    Ideal.ramificationIdx_eq_one_iff.mp
      ((Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓
        (Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot)).symm.trans hraK)
  let E : IntermediateField K L := IntermediateField.fixedField (Subgroup.zpowers σ)
  have hbridge :
      (arithFrobAt (𝓞 ↥E) Gal(L/(↥E)) 𝔓).restrictScalars K =
        arithFrobAt (𝓞 K) Gal(L/K) 𝔓 := by
    haveI : IsScalarTower K ↥E L := E.isScalarTower_mid'
    haveI : IsGalois (↥E) L := IsGalois.tower_top_intermediateField E
    haveI : IsGaloisGroup Gal(L/(↥E)) (↥E) L := IsGaloisGroup.of_isGalois (↥E) L
    haveI hPbot : 𝔓 ≠ ⊥ := by
      rintro rfl
      simp only [Ideal.under_bot, Ideal.ramificationIdx'_bot, zero_ne_one] at hraK
    haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
    set σFr := arithFrobAt (𝓞 ↥E) Gal(L/(↥E)) 𝔓 with hσFr
    have hKfrob1 : IsArithFrobAt (𝓞 K) (σFr.restrictScalars K) 𝔓 := by
      intro x
      have hact : (σFr.restrictScalars K) • x = σFr • x := Subtype.ext (by
        change (σFr.restrictScalars K) • (x : L) = σFr • (x : L)
        rw [AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.restrictScalars_apply])
      change (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) (σFr.restrictScalars K)) x
        - x ^ Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K)) ∈ 𝔓
      rw [show x ^ Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K))
            = x ^ Nat.card (𝓞 ↥E ⧸ 𝔓.under (𝓞 ↥E)) by rw [hnorm],
        show (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) (σFr.restrictScalars K)) x = σFr • x by
          rw [← hact]
          rfl]
      exact IsArithFrobAt.arithFrobAt (𝓞 ↥E) Gal(L/(↥E)) 𝔓 x
    have hmem := hKfrob1.mul_inv_mem_inertia (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓)
    rw [show Ideal.inertia Gal(L/K) 𝔓 = ⊥ from by
          have hPbot : 𝔓 ≠ ⊥ := by
            rintro rfl
            simp only [Ideal.under_bot, Ideal.ramificationIdx'_bot, zero_ne_one] at hraK
          have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
          have : 𝔓.IsMaximal := ‹𝔓.IsPrime›.isMaximal hPbot
          have : (𝔓.under (𝓞 K)).IsMaximal :=
            (inferInstance : (𝔓.under (𝓞 K)).IsPrime).isMaximal hpbot
          have : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
          have : Algebra.IsSeparable (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
            let : Field (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Ideal.Quotient.field _
            let : Field (𝓞 L ⧸ 𝔓) := Ideal.Quotient.field _
            exact IsGalois.to_isSeparable
          haveI : Finite (𝓞 K ⧸ 𝔓.under (𝓞 K)) :=
            Ideal.finiteQuotientOfFreeOfNeBot _ hpbot
          rw [Subgroup.eq_bot_iff_card,
            Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) (𝔓.under (𝓞 K)) 𝔓,
            Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 Gal(L/K),
            ← Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 hpbot]
          exact hraK,
        Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.mp hmem
  letI : FaithfulSMul Gal(L/K) (𝓞 L) := IsGaloisGroup.faithful (𝓞 K)
  have heq : σ = arithFrobAt (𝓞 K) Gal(L/K) 𝔓 :=
    MulSemiringAction.toAlgHom_injective (𝓞 K) (𝓞 L) <|
      AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hfrob
        (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) 𝔓.primeCompl_le_nonZeroDivisors
  rw [← heq] at hbridge
  exact AlgEquiv.restrictScalars_injective K (hbridge.trans hσE.symm)

/-- For a degree-one fibre prime `P` of `𝓞 E` (unramified in `L`, with `Frob^E_P = [σ_E]`),
there is a prime `𝔓` of `𝓞 L` above `P` whose `K`-Frobenius is `σ`. This is the surjective
half of `card_fibre_E_eq_card_fibre_L` and the witness `frobeniusClass_under_eq_of_mem_fibre`
runs through: lift `P` to a prime of `L`, transport its norm and inertia data down to `E`, and
bridge `Frob^E_𝔓 = σ_E` back to `Frob^K_𝔓 = σ` by unramified Frobenius uniqueness. -/
private theorem exists_arithFrobAt_over_fibrePrime
    (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hσE : letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      σE.restrictScalars K = σ)
    [IsMulCommutative Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))]
    (P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) [P.IsPrime]
    (hunrP : UnramifiedIn K L (P.under (𝓞 K)))
    (hPunr : UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P)
    (hPfrob : frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
      = ConjClasses.mk σE)
    (hPdeg : (P.under (𝓞 K)).inertiaDeg' P = 1) (hPbot : P ≠ ⊥) :
    ∃ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver P) (_ : 𝔓 ≠ ⊥),
      𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) = P ∧
        IsArithFrobAt (𝓞 K) σ 𝔓 := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
    IsGalois.tower_top_intermediateField _
  obtain ⟨𝔓, h𝔓p, hcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) P (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp
        (FaithfulSMul.algebraMap_injective
          (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) (𝓞 L))]
      exact bot_le)
  have h𝔓lo : 𝔓.LiesOver P := ⟨hcomap.symm⟩
  have h𝔓bot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hPbot 𝔓
  haveI := h𝔓p
  haveI := h𝔓lo
  have hPeq : 𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) = P :=
    h𝔓lo.over.symm
  haveI hPPE : 𝔓.LiesOver (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
    Ideal.over_under (A := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) (P := 𝔓)
  have hunderK : 𝔓.under (𝓞 K) = P.under (𝓞 K) := by
    rw [← Ideal.under_under (B := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) 𝔓, hPeq]
  have hunrK : UnramifiedIn K L (𝔓.under (𝓞 K)) := hunderK ▸ hunrP
  haveI : 𝔓.LiesOver (𝔓.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := 𝔓)
  have hinertPK1 : (𝔓.under (𝓞 K)).inertiaDeg'
      (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) = 1 := by
    rw [hPeq, hunderK]
    exact hPdeg
  have hraE : Ideal.ramificationIdx'
      (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓 = 1 :=
    (Ideal.ramificationIdx'_eq_ramificationIdx
        (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓
        (Ideal.IsIntegral.comap_ne_bot _ h𝔓bot)).trans
      (Ideal.ramificationIdx_eq_one_iff.mpr
        (hPunr.2 𝔓 (h𝔓p.isMaximal h𝔓bot) (hPeq ▸ hPPE)))
  have hnorm : Nat.card (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))
        ⧸ 𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
      = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K)) := by
    have hnP := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver
      (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) (𝔓.under (𝓞 K))
      inferInstance ((hunrK).1)
    simp only [Submodule.cardQuot_apply, Ideal.absNorm_apply] at hnP ⊢
    rw [hnP, hinertPK1, pow_one]
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 h𝔓bot
  have hfrEeqσE : arithFrobAt (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
      Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓 = σE := by
    letI : CommMonoid Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
      IsMulCommutative.instCommMonoid
    let E := IntermediateField.fixedField (Subgroup.zpowers σ)
    have hcl : frobeniusClass (↥E) L P =
        ConjClasses.mk (arithFrobAt (𝓞 E) Gal(L/(↥E)) 𝔓) := by
      let e : ∃ 𝔔 : Ideal (𝓞 L), 𝔔.IsPrime ∧ 𝔔.LiesOver P := by
        obtain ⟨𝔔, hq, hcomap⟩ :=
          Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) P (by
            rw [(RingHom.injective_iff_ker_eq_bot _).mp
              (FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 L))]
            exact bot_le)
        exact ⟨𝔔, hq, ⟨hcomap.symm⟩⟩
      let 𝔔 := Classical.choose e
      haveI : 𝔔.IsPrime := (Classical.choose_spec e).1
      have hqlo : 𝔔.LiesOver P := (Classical.choose_spec e).2
      haveI : Finite (𝓞 L ⧸ 𝔔) := Ideal.finiteQuotientOfFreeOfNeBot 𝔔
        (Ideal.ne_bot_of_liesOver_of_ne_bot hPunr.1 𝔔)
      rw [frobeniusClass, dif_pos ⟨‹P.IsPrime›, hPunr⟩]
      change ConjClasses.mk (arithFrobAt (𝓞 E) Gal(L/(↥E)) 𝔔) =
        ConjClasses.mk (arithFrobAt (𝓞 E) Gal(L/(↥E)) 𝔓)
      exact ConjClasses.mk_eq_mk_iff_isConj.mpr <|
        isConj_arithFrobAt (𝓞 E) Gal(L/(↥E)) 𝔔 𝔓
          (hqlo.over.symm.trans (hPeq ▸ hPPE).over)
    rw [hPfrob] at hcl
    exact isConj_iff_eq.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hcl.symm)
  have hfrobK : arithFrobAt (𝓞 K) Gal(L/K) 𝔓 = σ := by
    have hraK : Ideal.ramificationIdx' (𝔓.under (𝓞 K)) 𝔓 = 1 := by
      have hPbot := Ideal.ne_bot_of_liesOver_of_ne_bot hunrK.1 𝔓
      have hpbot := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
      haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
        hunrK.2 𝔓 (‹𝔓.IsPrime›.isMaximal hPbot) inferInstance
      rw [Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 hpbot]
      exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
    let E : IntermediateField K L := IntermediateField.fixedField (Subgroup.zpowers σ)
    have hbridge :
        (arithFrobAt (𝓞 ↥E) Gal(L/(↥E)) 𝔓).restrictScalars K =
          arithFrobAt (𝓞 K) Gal(L/K) 𝔓 := by
      haveI : IsScalarTower K ↥E L := E.isScalarTower_mid'
      haveI : IsGalois (↥E) L := IsGalois.tower_top_intermediateField E
      haveI : IsGaloisGroup Gal(L/(↥E)) (↥E) L := IsGaloisGroup.of_isGalois (↥E) L
      haveI hPbot : 𝔓 ≠ ⊥ := by
        rintro rfl
        simp only [Ideal.under_bot, Ideal.ramificationIdx'_bot, zero_ne_one] at hraK
      haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
      set σFr := arithFrobAt (𝓞 ↥E) Gal(L/(↥E)) 𝔓 with hσFr
      have hKfrob1 : IsArithFrobAt (𝓞 K) (σFr.restrictScalars K) 𝔓 := by
        intro x
        have hact : (σFr.restrictScalars K) • x = σFr • x := Subtype.ext (by
          change (σFr.restrictScalars K) • (x : L) = σFr • (x : L)
          rw [AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.restrictScalars_apply])
        change (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) (σFr.restrictScalars K)) x
          - x ^ Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K)) ∈ 𝔓
        rw [show x ^ Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K))
              = x ^ Nat.card (𝓞 ↥E ⧸ 𝔓.under (𝓞 ↥E)) by rw [hnorm],
          show (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) (σFr.restrictScalars K)) x = σFr • x by
            rw [← hact]
            rfl]
        exact IsArithFrobAt.arithFrobAt (𝓞 ↥E) Gal(L/(↥E)) 𝔓 x
      have hmem := hKfrob1.mul_inv_mem_inertia (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓)
      rw [show Ideal.inertia Gal(L/K) 𝔓 = ⊥ from by
            have hPbot : 𝔓 ≠ ⊥ := by
              rintro rfl
              simp only [Ideal.under_bot, Ideal.ramificationIdx'_bot, zero_ne_one] at hraK
            have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
            have : 𝔓.IsMaximal := ‹𝔓.IsPrime›.isMaximal hPbot
            have : (𝔓.under (𝓞 K)).IsMaximal :=
              (inferInstance : (𝔓.under (𝓞 K)).IsPrime).isMaximal hpbot
            have : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
            have : Algebra.IsSeparable (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
              let : Field (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Ideal.Quotient.field _
              let : Field (𝓞 L ⧸ 𝔓) := Ideal.Quotient.field _
              exact IsGalois.to_isSeparable
            haveI : Finite (𝓞 K ⧸ 𝔓.under (𝓞 K)) :=
              Ideal.finiteQuotientOfFreeOfNeBot _ hpbot
            rw [Subgroup.eq_bot_iff_card,
              Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) (𝔓.under (𝓞 K)) 𝔓,
              Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 Gal(L/K),
              ← Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 hpbot]
            exact hraK,
          Subgroup.mem_bot] at hmem
      exact mul_inv_eq_one.mp hmem
    rw [hfrEeqσE, hσE] at hbridge
    exact hbridge.symm
  exact ⟨𝔓, h𝔓p, hPeq ▸ hPPE, h𝔓bot, hPeq,
    hfrobK ▸ IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓⟩

/-- For a prime `𝔓` of `𝓞 L` above `𝔭` with `K`-Frobenius `σ`, its contraction `𝔓 ∩ 𝓞 E` is a
degree-one fibre prime: unramified in `L`, with `Frob^E = [σ_E]` and `f(· ∣ 𝔭) = 1`. This is
the forward (injective-side) map of the fibre bijection `card_fibre_E_eq_card_fibre_L`, run
through `inertiaDeg_under_E_eq_one_of_frobenius` and `arithFrobAt_E_eq_of_isArithFrobAt`. -/
private theorem under_E_mem_fibre_of_isArithFrobAt
    (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hσE : letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      σE.restrictScalars K = σ)
    [IsMulCommutative Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))]
    (horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭) (hPbot : 𝔓 ≠ ⊥)
    (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓) :
    haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) ∈
        {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
          P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
          frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
            = ConjClasses.mk σE ∧ (P.under (𝓞 K)).inertiaDeg' P = 1}
      ∧ (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))).LiesOver 𝔭
      ∧ (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) ≠ ⊥ := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
    IsGalois.tower_top_intermediateField _
  haveI := hP
  have hunderK : 𝔓.under (𝓞 K) = 𝔭 := hP.over.symm
  have hunrK : UnramifiedIn K L (𝔓.under (𝓞 K)) := hunderK ▸ hunr
  haveI : 𝔓.LiesOver (𝔓.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := 𝔓)
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
  obtain ⟨hraE, hinPK, hnorm⟩ :=
    inertiaDeg_under_E_eq_one_of_frobenius σ 𝔓 hunrK inferInstance hfrob horderE
  have hfrE := arithFrobAt_E_eq_of_isArithFrobAt σ σE hσE 𝔓 hunrK inferInstance hfrob horderE
    hraE hnorm
  have hunram : UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L
      (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) := by
    refine ⟨Ideal.IsIntegral.comap_ne_bot _ hPbot, fun 𝔔 h𝔔max h𝔔lo ↦ ?_⟩
    haveI := h𝔔max.isPrime
    have h𝔔eq : 𝔔 = 𝔓 := eq_of_liesOver_under_E_of_frobenius σ 𝔓 hunrK inferInstance hfrob
      horderE 𝔔 h𝔔lo
    subst h𝔔eq
    exact Ideal.ramificationIdx_eq_one_iff.mp
      ((Ideal.ramificationIdx'_eq_ramificationIdx
        (𝔔.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔔
        (Ideal.IsIntegral.comap_ne_bot _ hPbot)).symm.trans hraE)
  haveI hPEK : (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))).LiesOver 𝔭 := by
    haveI : (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))).LiesOver
        (𝔓.under (𝓞 K)) := inferInstance
    rwa [hunderK] at this
  haveI hPPE : 𝔓.LiesOver (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
    Ideal.over_under (A := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) (P := 𝔓)
  refine ⟨⟨inferInstance, hunram, ?_, ?_⟩, hPEK, Ideal.IsIntegral.comap_ne_bot _ hPbot⟩
  · let E := IntermediateField.fixedField (Subgroup.zpowers σ)
    letI : CommMonoid Gal(L/(↥E)) := IsMulCommutative.instCommMonoid
    let pE := 𝔓.under (𝓞 E)
    let e : ∃ 𝔔 : Ideal (𝓞 L), 𝔔.IsPrime ∧ 𝔔.LiesOver pE := by
      obtain ⟨𝔔, hq, hcomap⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) pE (by
          rw [(RingHom.injective_iff_ker_eq_bot _).mp
            (FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 L))]
          exact bot_le)
      exact ⟨𝔔, hq, ⟨hcomap.symm⟩⟩
    let 𝔔 := Classical.choose e
    haveI : 𝔔.IsPrime := (Classical.choose_spec e).1
    have hqlo : 𝔔.LiesOver pE := (Classical.choose_spec e).2
    haveI : Finite (𝓞 L ⧸ 𝔔) := Ideal.finiteQuotientOfFreeOfNeBot 𝔔
      (Ideal.ne_bot_of_liesOver_of_ne_bot hunram.1 𝔔)
    have hconj := isConj_arithFrobAt (𝓞 E) Gal(L/(↥E)) 𝔔 𝔓
      (hqlo.over.symm.trans hPPE.over)
    have heq := isConj_iff_eq.mp hconj
    rw [frobeniusClass, dif_pos ⟨inferInstance, hunram⟩]
    change ConjClasses.mk (arithFrobAt (𝓞 E) Gal(L/(↥E)) 𝔔) = ConjClasses.mk σE
    rw [heq, hfrE]
  · rw [show (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))).under (𝓞 K)
        = 𝔓.under (𝓞 K) from Ideal.under_under 𝔓]
    exact hinPK

/-- **Fibre bijection: degree-one `E`-primes with Frobenius `σ_E` ↔ `L`-primes with
Frobenius `σ`** (Sharifi 7.2.2 p. 143). For a prime `𝔭` of `𝓞 K` unramified in `L` with
Frobenius class `[σ]`, the map `𝔓 ↦ 𝔓 ∩ 𝓞 E` is a bijection from the primes `𝔓` of `𝓞 L`
above `𝔭` with `Frob^K_𝔓 = σ` onto the primes `P` of `𝓞 E` above `𝔭`, unramified in `L`,
with `Frob^E_P = [σ_E]` and `f(P ∣ 𝔭) = 1`. Hence the two fibres are equinumerous; combined
with the proven count `count_primes_above_with_frobenius_eq_sigma` this gives the number of
such `P` over `𝔭` as `|G|/(f·|C|)`. -/
private theorem card_fibre_E_eq_card_fibre_L
    (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hσE : letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      σE.restrictScalars K = σ)
    [IsMulCommutative Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))]
    (horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (_hCfrob : frobeniusClass K L 𝔭 = ConjClasses.mk σ) :
    haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    Nat.card {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
        P ∈ {P | P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
              ∧ frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
                = ConjClasses.mk σE
              ∧ (P.under (𝓞 K)).inertiaDeg' P = 1} ∧ P.LiesOver 𝔭 ∧ P ≠ ⊥}
      = Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
          IsArithFrobAt (𝓞 K) σ 𝔓} := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
    IsGalois.tower_top_intermediateField _
  refine (Nat.card_congr (Equiv.ofBijective
      (fun 𝔓 ↦ ⟨𝔓.1.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))),
        by obtain ⟨_, hP, hPbot, hfrob⟩ := 𝔓.2
           exact under_E_mem_fibre_of_isArithFrobAt σ σE hσE horderE 𝔭 hunr 𝔓.1 hP hPbot hfrob⟩)
      ⟨?_, ?_⟩)).symm
  · rintro ⟨𝔓₁, h𝔓₁, hP₁, hP₁bot, hfrob₁⟩ ⟨𝔓₂, h𝔓₂, hP₂, hP₂bot, hfrob₂⟩ hΦ
    haveI := h𝔓₁
    haveI := h𝔓₂
    haveI := hP₁
    haveI := hP₂
    have hunderK₁ : 𝔓₁.under (𝓞 K) = 𝔭 := hP₁.over.symm
    have hunrK₁ : UnramifiedIn K L (𝔓₁.under (𝓞 K)) := hunderK₁ ▸ hunr
    haveI : 𝔓₁.LiesOver (𝔓₁.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := 𝔓₁)
    have hΦ' : 𝔓₂.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))
        = 𝔓₁.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) :=
      congrArg Subtype.val hΦ |>.symm
    haveI hP₂lo : 𝔓₂.LiesOver
        (𝔓₁.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) := by
      haveI : 𝔓₂.LiesOver
        (𝔓₂.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
        Ideal.over_under (A := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) (P := 𝔓₂)
      rwa [hΦ'] at this
    exact Subtype.ext (eq_of_liesOver_under_E_of_frobenius σ 𝔓₁ hunrK₁ inferInstance hfrob₁
      horderE 𝔓₂ hP₂lo).symm
  · rintro ⟨P, ⟨hPp, hPunr, hPfrob, hPdeg⟩, hPlo, hPbot⟩
    haveI := hPp
    haveI := hPlo
    have hunrP : UnramifiedIn K L (P.under (𝓞 K)) := hPlo.over.symm ▸ hunr
    obtain ⟨𝔓, h𝔓p, h𝔓lo, h𝔓bot, hPeq, hfrobK⟩ :=
      exists_arithFrobAt_over_fibrePrime σ σE hσE P hunrP hPunr hPfrob hPdeg hPbot
    haveI := h𝔓p
    haveI := h𝔓lo
    have hunderK : 𝔓.under (𝓞 K) = 𝔭 := by
      rw [← Ideal.under_under (B := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) 𝔓,
        hPeq]
      exact hPlo.over.symm
    haveI hPK𝔓 : 𝔓.LiesOver 𝔭 := hunderK ▸ Ideal.over_under (A := 𝓞 K) (P := 𝔓)
    exact ⟨⟨𝔓, h𝔓p, hPK𝔓, h𝔓bot, hfrobK⟩, Subtype.ext hPeq⟩

/-- **A degree-one fibre prime has `K`-Frobenius class `[σ]`** (Sharifi 7.2.2 p. 143). If `P`
is a prime of `𝓞 E` above an unramified-in-`L` prime `𝔭 = P ∩ 𝓞 K`, unramified in `L`, with
`Frob^E_P = [σ_E]` and degree one over `K`, then the `K`-Frobenius class of `𝔭` is `[σ]`. -/
private theorem frobeniusClass_under_eq_of_mem_fibre
    (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hσE : letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      σE.restrictScalars K = σ)
    [IsMulCommutative Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))]
    (_horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) [P.IsPrime]
    (hunrP : UnramifiedIn K L (P.under (𝓞 K)))
    (hPunr : UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P)
    (hPfrob : frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
      = ConjClasses.mk σE)
    (hPdeg : (P.under (𝓞 K)).inertiaDeg' P = 1) (hPbot : P ≠ ⊥) :
    frobeniusClass K L (P.under (𝓞 K)) = ConjClasses.mk σ := by
  haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
    IsGalois.tower_top_intermediateField _
  obtain ⟨𝔓, h𝔓p, h𝔓lo, h𝔓bot, hPeq, hfrobK⟩ :=
    exists_arithFrobAt_over_fibrePrime σ σE hσE P hunrP hPunr hPfrob hPdeg hPbot
  haveI := h𝔓p
  haveI := h𝔓lo
  have hunderK : P.under (𝓞 K) = 𝔓.under (𝓞 K) := by
    rw [← hPeq, Ideal.under_under]
  have hunrK : UnramifiedIn K L (𝔓.under (𝓞 K)) := hunderK ▸ hunrP
  haveI : 𝔓.LiesOver (𝔓.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := 𝔓)
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 h𝔓bot
  have hclass : frobeniusClass K L (𝔓.under (𝓞 K)) =
      ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔓) := by
    let e : ∃ 𝔔 : Ideal (𝓞 L), 𝔔.IsPrime ∧ 𝔔.LiesOver (𝔓.under (𝓞 K)) := by
      obtain ⟨𝔔, hq, hcomap⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L)
          (𝔓.under (𝓞 K)) (by
            rw [(RingHom.injective_iff_ker_eq_bot _).mp
              (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))]
            exact bot_le)
      exact ⟨𝔔, hq, ⟨hcomap.symm⟩⟩
    let 𝔔 := Classical.choose e
    haveI : 𝔔.IsPrime := (Classical.choose_spec e).1
    have hqlo : 𝔔.LiesOver (𝔓.under (𝓞 K)) := (Classical.choose_spec e).2
    haveI : Finite (𝓞 L ⧸ 𝔔) := Ideal.finiteQuotientOfFreeOfNeBot 𝔔
      (Ideal.ne_bot_of_liesOver_of_ne_bot hunrK.1 𝔔)
    rw [frobeniusClass, dif_pos ⟨inferInstance, hunrK⟩]
    change ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔔) =
      ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔓)
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr <|
      isConj_arithFrobAt (𝓞 K) Gal(L/K) 𝔔 𝔓
        (hqlo.over.symm.trans (‹𝔓.LiesOver (𝔓.under (𝓞 K))›).over)
  haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
    hunrK.2 𝔓 (h𝔓p.isMaximal h𝔓bot) inferInstance
  letI : FaithfulSMul Gal(L/K) (𝓞 L) := IsGaloisGroup.faithful (𝓞 K)
  have hfrobEq : arithFrobAt (𝓞 K) Gal(L/K) 𝔓 = σ :=
    MulSemiringAction.toAlgHom_injective (𝓞 K) (𝓞 L) <|
      AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt
        (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) hfrobK
        𝔓.primeCompl_le_nonZeroDivisors
  rw [hunderK, hclass, hfrobEq]

/-- The fibre over an unramified `K`-prime `𝔭` with `Frob^K = [σ]` of the degree-one `E`-primes
with `Frob^E = [σ_E]` has cardinality `|G|/(f·|C|)`, i.e. `(f·|C|)·#fibre = |G|`. Combines the
fibre bijection `card_fibre_E_eq_card_fibre_L` with the count
`count_primes_above_with_frobenius_eq_sigma`. -/
private theorem card_fibre_T1_over_prime
    (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hσE : letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      σE.restrictScalars K = σ)
    [IsMulCommutative Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))]
    (horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr𝔭 : UnramifiedIn K L 𝔭)
    (hfrob𝔭 : frobeniusClass K L 𝔭 = ConjClasses.mk σ) :
    (orderOf σ * Nat.card (ConjClasses.mk σ).carrier) *
        Nat.card {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
          P ∈ {P | P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
                ∧ frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
                  = ConjClasses.mk σE ∧ (P.under (𝓞 K)).inertiaDeg' P = 1}
            ∧ P.LiesOver 𝔭 ∧ P ≠ ⊥}
      = Nat.card Gal(L/K) := by
  rw [card_fibre_E_eq_card_fibre_L σ σE hσE horderE 𝔭 hunr𝔭 hfrob𝔭, mul_comm, ← mul_assoc]
  exact count_primes_above_with_frobenius_eq_sigma K L σ (ConjClasses.mk σ) rfl 𝔭 hunr𝔭 hfrob𝔭

set_option backward.isDefEq.respectTransparency false in
/-- **LEAF A: the degree-one part of `T` carries the main term** (Sharifi 7.2.2 p. 143). For
`1 < s`, the partial Dirichlet sum over the set `T₁` of degree-one (over `K`) primes `P` of
`𝓞 E` above an unramified-in-`L` prime, with `Frob^E_P = [σ_E]`, equals `|G|/(f·|C|)` times the
partial sum over `S` (the primes of `𝓞 K` with `K`-Frobenius class `[σ]`).  The fibre over
each `𝔭 ∈ S` has exactly `|G|/(f·|C|)` such primes `P` (the fibre bijection
`card_fibre_E_eq_card_fibre_L` together with the proven count
`count_primes_above_with_frobenius_eq_sigma`), and `N P = N 𝔭` for degree-one `P`. -/
theorem primeIdealZetaSum_fibre_eq_smul
    (σ : Gal(L/K))
    (σE : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (hσE : letI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      σE.restrictScalars K = σ)
    [IsMulCommutative Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))]
    (horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    {s : ℝ} (hs : 1 < s) :
    haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    primeIdealZetaSum
        {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
          P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
          frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
            = ConjClasses.mk σE ∧ (P.under (𝓞 K)).inertiaDeg' P = 1 ∧
          UnramifiedIn K L (P.under (𝓞 K))} s
      = ((Nat.card Gal(L/K) : ℝ) / (orderOf σ * Nat.card (ConjClasses.mk σ).carrier))
        * primeIdealZetaSum {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
            frobeniusClass K L 𝔭 = ConjClasses.mk σ} s := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
    IsGalois.tower_top_intermediateField _
  set Sset := {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
    frobeniusClass K L 𝔭 = ConjClasses.mk σ} with hSset
  set T₁set := {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) |
    P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P ∧
    frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P = ConjClasses.mk σE ∧
    (P.under (𝓞 K)).inertiaDeg' P = 1 ∧ UnramifiedIn K L (P.under (𝓞 K))} with hT₁set
  set S' := {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ Sset ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} with hS'
  have hgmem : ∀ P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥},
      P.1.under (𝓞 K) ∈ Sset ∧ (P.1.under (𝓞 K)).IsPrime ∧ P.1.under (𝓞 K) ≠ ⊥ := by
    rintro ⟨P, ⟨hPp, hPunr, hPfrob, hPdeg, hunrP⟩, _, hPbot⟩
    haveI := hPp
    refine ⟨⟨inferInstance, hunrP, ?_⟩, inferInstance, (hunrP).1⟩
    exact frobeniusClass_under_eq_of_mem_fibre σ σE hσE horderE P hunrP hPunr hPfrob hPdeg hPbot
  set g : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥} → S' :=
    fun P ↦ ⟨P.1.under (𝓞 K), hgmem P⟩ with hg
  have hnormeq : ∀ P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥},
      (Ideal.absNorm P.1 : ℝ) = (Ideal.absNorm (P.1.under (𝓞 K)) : ℝ) := by
    rintro ⟨P, ⟨hPp, _, _, hPdeg, _⟩, _, hPbot⟩
    haveI := hPp
    have hpbot : P.under (𝓞 K) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
    haveI : P.LiesOver (P.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := P)
    have hpow := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P (P.under (𝓞 K)) inferInstance hpbot
    rw [hPdeg, pow_one] at hpow
    rw [hpow]
  have hcardfib : ∀ 𝔭 : S', (orderOf σ * Nat.card (ConjClasses.mk σ).carrier) *
      Nat.card {P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥} // g P = 𝔭} = Nat.card Gal(L/K) := by
    intro 𝔭
    obtain ⟨hp𝔭, hunr𝔭, hfrob𝔭⟩ := 𝔭.2.1
    haveI := hp𝔭
    have hreindex : Nat.card {P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥} // g P = 𝔭}
        = Nat.card {P : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) //
            P ∈ {P | P.IsPrime ∧ UnramifiedIn ↥(IntermediateField.fixedField (Subgroup.zpowers σ))
                  L P ∧ frobeniusClass ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L P
                  = ConjClasses.mk σE ∧ (P.under (𝓞 K)).inertiaDeg' P = 1}
              ∧ P.LiesOver 𝔭.1 ∧ P ≠ ⊥} := by
      refine Nat.card_congr ⟨fun x ↦ ⟨x.1.1, ?_, ?_, x.1.2.2.2⟩,
        fun y ↦ ⟨⟨y.1, ?_, y.2.1.1, y.2.2.2⟩, ?_⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
      · exact ⟨x.1.2.1.1, x.1.2.1.2.1, x.1.2.1.2.2.1, x.1.2.1.2.2.2.1⟩
      · exact ⟨(congrArg Subtype.val x.2).symm ▸ (Ideal.over_under (A := 𝓞 K) (P := x.1.1)).over⟩
      · haveI := y.2.1.1
        have hunderK : y.1.under (𝓞 K) = 𝔭.1 := (y.2.2.1).over.symm
        exact ⟨y.2.1.1, y.2.1.2.1, y.2.1.2.2.1, y.2.1.2.2.2, by rw [hunderK]; exact hunr𝔭⟩
      · exact Subtype.ext (y.2.2.1).over.symm
    rw [hreindex]
    exact card_fibre_T1_over_prime σ σE hσE horderE 𝔭.1 hunr𝔭 hfrob𝔭
  have hfibfin : ∀ 𝔭 : S', Finite {P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥} // g P = 𝔭} := by
    intro 𝔭
    haveI := 𝔭.2.2.1
    haveI : 𝔭.1.IsMaximal := 𝔭.2.2.1.isMaximal 𝔭.2.2.2
    haveI : Finite (𝔭.1.primesOver
        (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) :=
      (IsDedekindDomain.primesOver_finite 𝔭.1 _).to_subtype
    refine Finite.of_injective (β := 𝔭.1.primesOver
        (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
      (fun P ↦ ⟨P.1.1, P.1.2.2.1, ?_⟩) ?_
    · haveI := P.1.2.2.1
      exact ⟨(congrArg Subtype.val P.2).symm ▸ (Ideal.over_under (A := 𝓞 K) (P := P.1.1)).over⟩
    · rintro ⟨⟨P, hP⟩, hgP⟩ ⟨⟨Q, hQ⟩, hgQ⟩ hPQ
      simpa using hPQ
  have hordC_pos : (0 : ℝ) < orderOf σ * Nat.card (ConjClasses.mk σ).carrier := by
    have h₁ : 0 < orderOf σ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
    have : Nonempty (ConjClasses.mk σ).carrier := ⟨⟨σ, ConjClasses.mem_carrier_mk⟩⟩
    have h₂ : 0 < Nat.card (ConjClasses.mk σ).carrier := Nat.card_pos
    positivity
  set h : S' → ℝ := fun 𝔭 ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) with hh
  have hequivfib : ∀ 𝔭 : S', (g ⁻¹' {𝔭} : Set _) ≃
      {P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥} // g P = 𝔭} :=
    fun 𝔭 ↦ Equiv.subtypeEquivRight fun _ ↦ Iff.rfl
  have hcard : ∀ 𝔭 : S', (Nat.card (g ⁻¹' {𝔭} : Set _) : ℝ)
      = (Nat.card Gal(L/K) : ℝ) / (orderOf σ * Nat.card (ConjClasses.mk σ).carrier) := by
    intro 𝔭
    rw [Nat.card_congr (hequivfib 𝔭), eq_div_iff hordC_pos.ne', mul_comm, ← hcardfib 𝔭]
    push_cast
    ring
  rw [primeIdealZetaSum, primeIdealZetaSum,
    tsum_congr (fun P ↦ congrArg (· ^ (-s)) (hnormeq P)),
    show (fun P : {P // P ∈ T₁set ∧ P.IsPrime ∧ P ≠ ⊥} ↦
      (Ideal.absNorm (P.1.under (𝓞 K)) : ℝ) ^ (-s)) = (fun P ↦ h (g P)) from rfl]
  have hsumm : Summable fun P ↦ h (g P) :=
    ((show ∀ (S : Set (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
      intro S s hs
      exact (((show Summable (fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s)) from
        (((show HasSum (fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))) (NumberField.dedekindZeta ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) (s : ℂ)) from by
          have hcondition : 1 < ((s : ℂ)).re := (by simpa using hs)
          classical
          haveI (n : ℕ) : Finite {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} :=
            Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ I.1)
              ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
              (fun _ _ _ _ ↦ Subtype.ext)
          have hseries : Summable fun n : ℕ ↦ ‖(idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ := by
            classical
            have hbig : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) k : ℝ))
                =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
              classical
              have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) | Ideal.absNorm I.1 = b}.Finite := fun b ↦
                Set.Finite.preimage (f := fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ I.1) (fun _ _ _ _ ↦ Subtype.ext)
                  (Ideal.finite_setOf_absNorm_eq (S := 𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) b)
              have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) k =
                  Nat.card {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 ≤ n} := fun n ↦ by
                have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦
                  Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ ↦ h_finite b)
                rw [show ((fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
                    {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) | Ideal.absNorm I.1 ≤ n} by
                  ext ⟨I, hI⟩
                  simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_setOf_eq]
                  exact ⟨fun h ↦ h.2, fun h ↦
                    ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
                exact key.symm
              have h_card_bridge : ∀ n : ℕ,
                  Nat.card {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 ≤ n} =
                  Nat.card {I : (Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
                fun n ↦ Nat.card_congr
                  { toFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                      ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
                    invFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                      ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
                    left_inv := fun _ ↦ rfl
                    right_inv := fun _ ↦ rfl }
              refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
                (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ ↥(IntermediateField.fixedField (Subgroup.zpowers σ))).comp
                  tendsto_natCast_atTop_atTop).congr' ?_)
              filter_upwards with n
              simp only [Function.comp_apply, Real.rpow_one]
              rw [← Nat.cast_sum, h_sum_card n, h_card_bridge n]
              push_cast
              rfl
            have h_lss : LSeriesSummable (fun n : ℕ ↦ ((idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℝ) : ℂ)) s :=
              LSeriesSummable_of_sum_norm_bigO_and_nonneg
                (f := fun n ↦ (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℝ))
                hbig (fun _ ↦ Nat.cast_nonneg _) zero_le_one
                (by exact_mod_cast hcondition)
            have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℝ) : ℂ)) (s : ℂ) =
                fun n ↦ (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
              funext n
              simp only [LSeries.term]
              split_ifs with hn
              · subst hn
                have hzero : idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) 0 = 0 := by
                    unfold idealNormMultiplicity
                    rw [Nat.card_eq_zero]
                    exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
                simp [hzero]
              · simp [Complex.cpow_neg, div_eq_mul_inv]
            exact (h_term_eq ▸ h_lss :
              Summable fun n ↦ (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ))).norm
          have hzeta : NumberField.dedekindZeta ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) (s : ℂ) =
              ∑' n : ℕ, (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
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
              have hzero : idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) 0 = 0 := by
                  unfold idealNormMultiplicity
                  rw [Nat.card_eq_zero]
                  exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
              simp [hzero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
            · simp only [hn.ne', ↓reduceIte]
              rw [Complex.cpow_neg, div_eq_mul_inv]
              congr 1
              unfold idealNormMultiplicity
              have hequiv : {I : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) // Ideal.absNorm I = n} ≃
                  {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} := by
                refine {
                  toFun := fun ⟨I, hI⟩ ↦ ⟨⟨I, ?_⟩, hI⟩
                  invFun := fun ⟨⟨I, _⟩, hI⟩ ↦ ⟨I, hI⟩
                  left_inv := fun _ ↦ rfl
                  right_inv := fun _ ↦ rfl }
                intro h
                rw [h, Ideal.absNorm_bot] at hI
                lia
              exact_mod_cast Nat.card_congr hequiv
          set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ Ideal.absNorm I.1)
          have hval : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n},
              (Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))) = (idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) :=
            fun n ↦ by
              rw [show (∑' y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n},
                  (Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))) = idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n • (n : ℂ) ^ (-(s : ℂ)) from
                (tsum_congr fun y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
                  (tsum_const ((n : ℂ) ^ (-(s : ℂ)))), nsmul_eq_mul]
          have hnorm : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n},
              ‖(Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))‖) = ‖(idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ :=
            fun n ↦ by
              rw [show (∑' y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n},
                  ‖(Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))‖) = idealNormMultiplicity ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) n • ‖(n : ℂ) ^ (-(s : ℂ))‖ from
                (tsum_congr fun y : {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
                  (tsum_const ‖(n : ℂ) ^ (-(s : ℂ))‖), nsmul_eq_mul, norm_mul,
                Complex.norm_natCast]
          have hsummable : Summable fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ ‖(Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))‖ := by
            rw [← e.summable_iff]
            refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun _ ↦ Summable.of_finite, ?_⟩
            exact hseries.congr fun n ↦ (hnorm n).symm
          have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) // Ideal.absNorm I.1 = n} ↦
              (Ideal.absNorm (e p).1 : ℂ) ^ (-(s : ℂ)) :=
            (e.summable_iff (f := fun I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))).mpr
              hsummable.of_norm
          have hval_sum : (∑' I : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ)), (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))
              = NumberField.dedekindZeta ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) s := by
            rw [hzeta,
              ← e.tsum_eq (fun I ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))), hsummable_sigma.tsum_sigma]
            exact tsum_congr hval
          exact hval_sum ▸ hsummable.of_norm.hasSum)).summable.norm).congr
          fun I ↦ (Complex.norm_natCast_cpow_of_pos
            (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2)) _).trans <| by simp)).comp_injective
        (i := fun 𝔭 : {𝔭 : Ideal (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
          (⟨𝔭.1, 𝔭.2.2.2⟩ : NonzeroIdeal ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
        fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) T₁set hs).congr
      fun P ↦ congrArg (· ^ (-s)) (hnormeq P)
  rw [← (hsumm.hasSum.tsum_fiberwise g).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun 𝔭 ↦ ?_
  haveI := hfibfin 𝔭
  haveI : Finite (g ⁻¹' {𝔭} : Set _) :=
    Finite.of_equiv _ (hequivfib 𝔭).symm
  letI := Fintype.ofFinite (g ⁻¹' {𝔭} : Set _)
  rw [tsum_congr fun P : (g ⁻¹' {𝔭} : Set _) ↦ congrArg h P.2, tsum_fintype,
    Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul,
    hcard, mul_comm]

end Chebotarev
