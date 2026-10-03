/- GID: D5/S3/Factorization/Galois/Chebotarev/FixedFieldFrobeniusCounting
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/Chebotarev/FixedFieldFrobeniusCounting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A Frobenius-order condition forces uniqueness of a prime over the cyclic fixed-field prime. -/
module

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

open Filter NumberField Topology Set

open scoped ENNReal Pointwise

namespace Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- Sharifi 7.2.2 Step 1, above-counting (p. 143). Verbatim source quote:
"exactly `|G|/f|C|` of these have Frobenius σ". For a prime `𝔭` of
`𝓞 K` with Frobenius class `C` and a representative `σ ∈ C`, the count
of primes `𝔓` of `𝓞 L` above `𝔭` with `Frob_𝔓 = σ` is `|G|/(f·|C|)`.

This is the substantive new sub-lemma for the conjugacy-class →
cyclic reduction; the fixed-field cyclic-subextension setup
(`E = L^⟨σ⟩`, `[L:E] = ord σ`) is mathlib's `IntermediateField.fixedField`
and `IsGalois.card_aut_eq_finrank` applied at `⟨σ⟩`, and the density-lift
formula `δ_K(S) = (f|C|/|G|) δ_E(T_σ)` follows from this counting
together with `Σ N𝔭^{-s} ~ Σ NP^{-s}` (Sharifi 7.1.12 applied to both
`K` and `E`). -/
theorem count_primes_above_with_frobenius_eq_sigma
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : Gal(L/K)) (C : ConjClasses Gal(L/K)) (_hσ : ConjClasses.mk σ = C)
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭)
    (_hCfrob : frobeniusClass K L 𝔭 = C) :
    Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭)
        (_ : 𝔓 ≠ ⊥), IsArithFrobAt (𝓞 K) σ 𝔓}
      * orderOf σ * Nat.card C.carrier
      = Nat.card Gal(L/K) := by
  rw [mul_right_comm,
    (show ∀ (σ : Gal(L/K)) (C : ConjClasses Gal(L/K)) (_hσ : ConjClasses.mk σ = C) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (_hCfrob : frobeniusClass K L 𝔭 = C), (Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥), IsArithFrobAt (𝓞 K) σ 𝔓} * Nat.card C.carrier = Nat.card {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥}) from by
      intro σ C _hσ 𝔭 analyticInstance0 hunr _hCfrob
      classical
      exact
        (mul_comm _ _).trans ((show ∀ (σ : Gal(L/K)) (C : ConjClasses Gal(L/K)) (hσ : ConjClasses.mk σ = C) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hCfrob : frobeniusClass K L 𝔭 = C) (hequi : ∀ σ' : Gal(L/K), IsConj σ σ' → Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥), IsArithFrobAt (𝓞 K) σ 𝔓} = Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥), IsArithFrobAt (𝓞 K) σ' 𝔓}), (Nat.card {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} = Nat.card C.carrier * Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥), IsArithFrobAt (𝓞 K) σ 𝔓}) from by
          intro σ C hσ 𝔭 analyticInstance0 hunr hCfrob hequi
          classical
          have hpbot : 𝔭 ≠ ⊥ := (hunr).1
          haveI : 𝔭.IsMaximal := ‹𝔭.IsPrime›.isMaximal hpbot
          haveI : Finite (𝔭.primesOver (𝓞 L)) := (IsDedekindDomain.primesOver_finite 𝔭 (𝓞 L)).to_subtype
          haveI : Finite {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} :=
            Finite.of_injective
              (fun 𝔓 : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} ↦
                (⟨𝔓.1, 𝔓.2.1, 𝔓.2.2.1⟩ : 𝔭.primesOver (𝓞 L)))
              fun _ _ hab ↦ Subtype.ext
                (congrArg (fun q : 𝔭.primesOver (𝓞 L) ↦ q.1) hab)
          haveI : Fintype C.carrier := Fintype.ofFinite _
          have hfinP : ∀ (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭), Finite (𝓞 L ⧸ 𝔓) :=
            fun 𝔓 _ hP ↦ Ideal.finiteQuotientOfFreeOfNeBot 𝔓
              (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓)
          have hmem : ∀ (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭),
              haveI := hfinP 𝔓 hP
              arithFrobAt (𝓞 K) Gal(L/K) 𝔓 ∈ C.carrier := by
            intro 𝔓 _ hP
            haveI := hfinP 𝔓 hP
            have hclass : frobeniusClass K L 𝔭 =
                ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔓) := by
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
              change ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀) =
                ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔓)
              exact ConjClasses.mk_eq_mk_iff_isConj.mpr <|
                isConj_arithFrobAt (𝓞 K) Gal(L/K) 𝔓₀ 𝔓 (hlo₀.over.symm.trans hP.over)
            rw [ConjClasses.mem_carrier_iff_mk_eq, ← hclass, hCfrob]
          have hconj : ∀ g : C.carrier, IsConj σ g.1 := by
            rintro ⟨g, hg⟩
            rw [ConjClasses.mem_carrier_iff_mk_eq] at hg
            exact ConjClasses.mk_eq_mk_iff_isConj.mp (hσ.trans hg.symm)
          let F : {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} → C.carrier := fun 𝔓 ↦
            haveI := 𝔓.2.1
            haveI := hfinP 𝔓.1 𝔓.2.2.1
            ⟨arithFrobAt (𝓞 K) Gal(L/K) 𝔓.1, hmem 𝔓.1 𝔓.2.2.1⟩
          rw [← Nat.card_congr (Equiv.sigmaFiberEquiv F), Nat.card_sigma]
          have hfib : ∀ g : C.carrier,
              Nat.card {𝔓 // F 𝔓 = g}
                = Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥),
                    IsArithFrobAt (𝓞 K) σ 𝔓} := by
            intro g
            rw [hequi g.1 (hconj g)]
            refine Nat.card_congr ⟨fun x ↦ ⟨x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2, ?_⟩,
              fun x ↦ ⟨⟨x.1, by obtain ⟨hp, hP, hne, _⟩ := x.2; exact ⟨hp, hP, hne⟩⟩, ?_⟩,
              fun _ ↦ rfl, fun _ ↦ rfl⟩
            · haveI := x.1.2.1
              haveI := hfinP x.1.1 x.1.2.2.1
              rw [← Subtype.ext_iff.mp x.2]
              exact IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) x.1.1
            · obtain ⟨hp, hP, hne, hg⟩ := x.2
              haveI := hp
              haveI := hP
              haveI := hfinP x.1 hP
              haveI : Algebra.IsUnramifiedAt (𝓞 K) x.1 :=
                hunr.2 x.1 (hp.isMaximal hne) hP
              letI : FaithfulSMul Gal(L/K) (𝓞 L) := IsGaloisGroup.faithful (𝓞 K)
              exact Subtype.ext (MulSemiringAction.toAlgHom_injective (𝓞 K) (𝓞 L) <|
                AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hg
                  (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) x.1)
                  x.1.primeCompl_le_nonZeroDivisors).symm
          simp_rw [hfib]
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]) σ C _hσ 𝔭 hunr
          _hCfrob fun σ' hc ↦ (show ∀ (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (_hunr : UnramifiedIn K L 𝔭) (σ σ' : Gal(L/K)) (hc : IsConj σ σ'), (Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥), IsArithFrobAt (𝓞 K) σ 𝔓} = Nat.card {𝔓 : Ideal (𝓞 L) // ∃ (_ : 𝔓.IsPrime) (_ : 𝔓.LiesOver 𝔭) (_ : 𝔓 ≠ ⊥), IsArithFrobAt (𝓞 K) σ' 𝔓}) from by
            intro 𝔭 analyticInstance0 _hunr σ σ' hc
            classical
            obtain ⟨c, hc⟩ := isConj_iff.mp hc
            refine Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm c) fun 𝔓 ↦ ?_)
            simp only [MulAction.toPerm_apply]
            constructor
            · rintro ⟨hp, hP, hne, hfrob⟩
              haveI := hp
              haveI := hP
              refine ⟨inferInstance, inferInstance, ?_, ?_⟩
              · rw [← Ideal.smul_bot c]
                exact (MulAction.injective c).ne hne
              · exact hc ▸ hfrob.conj c
            · rintro ⟨hp, hP, hne, hfrob⟩
              haveI := hp
              haveI := hP
              have hsmul : c⁻¹ • (c • 𝔓) = 𝔓 := inv_smul_smul c 𝔓
              haveI hp' : 𝔓.IsPrime := hsmul ▸ (inferInstance : (c⁻¹ • (c • 𝔓)).IsPrime)
              haveI hP' : 𝔓.LiesOver 𝔭 := hsmul ▸ (inferInstance : (c⁻¹ • (c • 𝔓)).LiesOver 𝔭)
              have hne' : 𝔓 ≠ ⊥ := by
                rw [← hsmul, ← Ideal.smul_bot c⁻¹]
                exact (MulAction.injective c⁻¹).ne hne
              refine ⟨hp', hP', hne', ?_⟩
              have hconj := hfrob.conj c⁻¹
              rwa [hsmul, ← hc, show c⁻¹ * (c * σ * c⁻¹) * c⁻¹⁻¹ = σ by group] at hconj) 𝔭 hunr σ σ' hc).symm) σ C _hσ 𝔭 hunr _hCfrob]
  have hcard : Nat.card {𝔓 : Ideal (𝓞 L) //
      𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} * orderOf σ = Nat.card Gal(L/K) := by
    obtain ⟨𝔓₀, hp₀, hcomap₀⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔭 (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp
          (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))]
        exact bot_le)
    have hlo₀ : 𝔓₀.LiesOver 𝔭 := ⟨hcomap₀.symm⟩
    haveI : 𝔓₀.IsPrime := hp₀
    have hresidue :
        Module.finrank (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) (𝓞 L ⧸ 𝔓₀) = orderOf σ := by
      have hσ : ConjClasses.mk σ = C := _hσ
      have hCfrob : frobeniusClass K L 𝔭 = C := _hCfrob
      let 𝔓 := 𝔓₀
      have hlo : 𝔓.LiesOver 𝔭 := hlo₀
      have hra : Ideal.ramificationIdx' (𝔓.under (𝓞 K)) 𝔓 = 1 := by
        have hPbot := Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓
        have hpbot := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
        haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
          hunr.2 𝔓 (‹𝔓.IsPrime›.isMaximal hPbot) hlo
        rw [Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 hpbot]
        exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
      have : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓
        (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓)
      have hclass : frobeniusClass K L 𝔭 =
          ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔓) := by
        let e : ∃ 𝔓₁ : Ideal (𝓞 L), 𝔓₁.IsPrime ∧ 𝔓₁.LiesOver 𝔭 := by
          obtain ⟨𝔓₁, hp₁, hcomap₁⟩ :=
            Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L) 𝔭 (by
              rw [(RingHom.injective_iff_ker_eq_bot _).mp
                (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))]
              exact bot_le)
          exact ⟨𝔓₁, hp₁, ⟨hcomap₁.symm⟩⟩
        let 𝔓₁ := Classical.choose e
        haveI : 𝔓₁.IsPrime := (Classical.choose_spec e).1
        have hlo₁ : 𝔓₁.LiesOver 𝔭 := (Classical.choose_spec e).2
        haveI : Finite (𝓞 L ⧸ 𝔓₁) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓₁
          (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓₁)
        rw [frobeniusClass, dif_pos ⟨‹𝔭.IsPrime›, hunr⟩]
        change ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔓₁) =
          ConjClasses.mk (arithFrobAt (𝓞 K) Gal(L/K) 𝔓)
        exact ConjClasses.mk_eq_mk_iff_isConj.mpr <|
          isConj_arithFrobAt (𝓞 K) Gal(L/K) 𝔓₁ 𝔓 (hlo₁.over.symm.trans hlo.over)
      obtain ⟨c, hc⟩ : IsConj (arithFrobAt (𝓞 K) Gal(L/K) 𝔓) σ := by
        rw [← ConjClasses.mk_eq_mk_iff_isConj,
          ← hclass, hCfrob, hσ]
      have horder : orderOf (arithFrobAt (𝓞 K) Gal(L/K) 𝔓) =
          Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
        have h : Ideal.ramificationIdx' (𝔓.under (𝓞 K)) 𝔓 = 1 := hra
        have hPbot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓
        have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
        have : 𝔓.IsMaximal := ‹𝔓.IsPrime›.isMaximal hPbot
        have : (𝔓.under (𝓞 K)).IsMaximal :=
          (inferInstance : (𝔓.under (𝓞 K)).IsPrime).isMaximal hpbot
        have : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
        have : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
          Ideal.ramificationIdx_eq_one_iff.mp
            ((Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 hpbot).symm.trans h)
        let : Field (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Ideal.Quotient.field _
        let : Field (𝓞 L ⧸ 𝔓) := Ideal.Quotient.field _
        have : Finite (𝓞 K ⧸ 𝔓.under (𝓞 K)) :=
          Ideal.finiteQuotientOfFreeOfNeBot (𝔓.under (𝓞 K)) hpbot
        have : Algebra.IsSeparable (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) :=
          IsGalois.to_isSeparable
        have : Algebra.IsAlgebraic (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) :=
          Algebra.IsAlgebraic.of_finite _ _
        let : Fintype (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Fintype.ofFinite _
        set g₀ : MulAction.stabilizer Gal(L/K) 𝔓 :=
          ⟨arithFrobAt (𝓞 K) Gal(L/K) 𝔓,
            IsArithFrobAt.arithFrobAt_mem_stabilizer (𝓞 K) Gal(L/K) 𝔓⟩ with hg₀
        have hres :
            Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K) g₀ =
              FiniteField.frobeniusAlgEquivOfAlgebraic
                (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
          ext x
          obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
          rw [hg₀, Ideal.Quotient.stabilizerHom_apply,
            FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ← Nat.card_eq_fintype_card]
          exact (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓).mk_apply b
        have hinj :
            Function.Injective (Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K)) := by
          rw [← MonoidHom.ker_eq_bot_iff, Ideal.Quotient.ker_stabilizerHom]
          show (Ideal.inertia Gal(L/K) 𝔓).subgroupOf (MulAction.stabilizer Gal(L/K) 𝔓) = ⊥
          rw [show Ideal.inertia Gal(L/K) 𝔓 = ⊥ from by
            rw [Subgroup.eq_bot_iff_card,
              Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) (𝔓.under (𝓞 K)) 𝔓,
              Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 Gal(L/K),
              ← Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 hpbot]
            exact h,
            Subgroup.bot_subgroupOf]
        calc
          orderOf (arithFrobAt (𝓞 K) Gal(L/K) 𝔓) = orderOf g₀ := by
            rw [hg₀, Subgroup.orderOf_mk]
          _ = orderOf (Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K) g₀) :=
              (orderOf_injective _ hinj g₀).symm
          _ = orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic
                (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓)) := by rw [hres]
          _ = Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) :=
              FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic _ _
      rw [← hc.orderOf_eq, horder]
    rw [← hresidue]
    have hcard : Nat.card {𝔓 : Ideal (𝓞 L) //
          𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} *
        Module.finrank (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) (𝓞 L ⧸ 𝔓₀) =
          Nat.card Gal(L/K) := by
      have hlo : 𝔓₀.LiesOver 𝔭 := hlo₀
      have hpbot : 𝔭 ≠ ⊥ := (hunr).1
      have he : Ideal.ramificationIdx' (𝔓₀.under (𝓞 K)) 𝔓₀ = 1 := by
        have hPbot := Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓₀
        have hpbot := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
        haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓₀ :=
          hunr.2 𝔓₀ (‹𝔓₀.IsPrime›.isMaximal hPbot) hlo
        rw [Ideal.ramificationIdx'_eq_ramificationIdx (𝔓₀.under (𝓞 K)) 𝔓₀ hpbot]
        exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
      have hP0bot : 𝔓₀ ≠ ⊥ := by
        intro hbot
        subst 𝔓₀
        simp only [Ideal.under_bot, Ideal.ramificationIdx'_bot, zero_ne_one] at he
      have hunder : 𝔓₀.under (𝓞 K) = 𝔭 := hlo.over.symm
      have hp_under_bot : 𝔓₀.under (𝓞 K) ≠ ⊥ := hunder ▸ hpbot
      have : 𝔓₀.IsMaximal := ‹𝔓₀.IsPrime›.isMaximal hP0bot
      have : (𝔓₀.under (𝓞 K)).IsMaximal :=
        (inferInstance : (𝔓₀.under (𝓞 K)).IsPrime).isMaximal hp_under_bot
      have : Finite (𝓞 L ⧸ 𝔓₀) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓₀
        (Ideal.ne_bot_of_liesOver_of_ne_bot hunr.1 𝔓₀)
      have : Algebra.IsSeparable (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) (𝓞 L ⧸ 𝔓₀) := by
        let : Field (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) := Ideal.Quotient.field _
        let : Field (𝓞 L ⧸ 𝔓₀) := Ideal.Quotient.field _
        exact IsGalois.to_isSeparable
      haveI : Finite (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) :=
        Ideal.finiteQuotientOfFreeOfNeBot _ hp_under_bot
      have H :=
        Ideal.ncard_primesOver_mul_card_inertia_mul_finrank
          (G := Gal(L/K)) (𝔓₀.under (𝓞 K)) 𝔓₀
      rw [show Ideal.inertia Gal(L/K) 𝔓₀ = ⊥ from by
            rw [Subgroup.eq_bot_iff_card,
              Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) (𝔓₀.under (𝓞 K)) 𝔓₀,
              Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓₀.under (𝓞 K)) 𝔓₀ Gal(L/K),
              ← Ideal.ramificationIdx'_eq_ramificationIdx (𝔓₀.under (𝓞 K)) 𝔓₀ hp_under_bot]
            exact he,
          Subgroup.card_bot, mul_one,
          ← Ideal.inertiaDeg'_eq_inertiaDeg (𝔓₀.under (𝓞 K)) 𝔓₀,
          Ideal.inertiaDeg'_algebraMap (𝔓₀.under (𝓞 K)) 𝔓₀] at H
      have hset : (𝔓₀.under (𝓞 K)).primesOver (𝓞 L)
          = {𝔓 : Ideal (𝓞 L) | 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} := by
        ext 𝔓
        refine ⟨fun ⟨hp, hlo'⟩ ↦ ?_, fun ⟨hp, hlo', _⟩ ↦ ?_⟩
        · have := hlo'
          exact ⟨hp, hunder ▸ hlo', Ideal.ne_bot_of_liesOver_of_ne_bot hp_under_bot 𝔓⟩
        · exact ⟨hp, hunder ▸ hlo'⟩
      rwa [hset, ← Nat.card_coe_set_eq] at H
    exact hcard
  exact hcard

/-- **The decomposition group of `𝔓` equals `Gal(L/E)`** (Sharifi 7.2.2 p. 143, "`P` is by
definition inert in `L`"). For an unramified `𝔓` of `𝓞 L` over `𝔭 = 𝔓 ∩ 𝓞 K` whose
`K`-Frobenius is `σ`, with `E = L^⟨σ⟩` and `f = ord σ = [L : E]`, the decomposition group
`D_𝔓 = stab_{Gal(L/K)} 𝔓` is cyclic of order `f` generated by `Frob^K_𝔓 = σ`, hence equals
`⟨σ⟩ = fixingSubgroup E`. Therefore the stabiliser of `𝔓` inside `Gal(L/E)` is everything:
every `E`-automorphism fixes `𝔓` (its restriction to `K` lies in `⟨σ⟩ = D_𝔓`). In particular
`𝔓` is the unique prime of `𝓞 L` above `𝔓 ∩ 𝓞 E`. -/
private theorem stabilizer_intermediate_eq_top_of_frobenius
    (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hunrK : UnramifiedIn K L (𝔓.under (𝓞 K))) (hPK : 𝔓.LiesOver (𝔓.under (𝓞 K)))
    (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓)
    (_horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))) :
    haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    MulAction.stabilizer
        Gal(L/↥(IntermediateField.fixedField (Subgroup.zpowers σ))) 𝔓 = ⊤ := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  have hraK : Ideal.ramificationIdx' (𝔓.under (𝓞 K)) 𝔓 = 1 := by
    have hPbot := Ideal.ne_bot_of_liesOver_of_ne_bot hunrK.1 𝔓
    have hpbot := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
    haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
      hunrK.2 𝔓 (‹𝔓.IsPrime›.isMaximal hPbot) hPK
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 hpbot]
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have hPbot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hunrK.1 𝔓
  have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := (hunrK).1
  haveI : 𝔓.IsMaximal := ‹𝔓.IsPrime›.isMaximal hPbot
  haveI : (𝔓.under (𝓞 K)).IsMaximal :=
    (inferInstance : (𝔓.under (𝓞 K)).IsPrime).isMaximal hpbot
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
  haveI : Algebra.IsSeparable (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
    letI : Field (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Ideal.Quotient.field _
    letI : Field (𝓞 L ⧸ 𝔓) := Ideal.Quotient.field _
    exact IsGalois.to_isSeparable
  have hmem : σ ∈ MulAction.stabilizer Gal(L/K) 𝔓 := hfrob.mem_stabilizer
  have horder : orderOf σ =
      Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
    have h : Ideal.ramificationIdx' (𝔓.under (𝓞 K)) 𝔓 = 1 := hraK
    have hσ : IsArithFrobAt (𝓞 K) σ 𝔓 := hfrob
    have hPbot : 𝔓 ≠ ⊥ := by
      rintro rfl
      simp only [Ideal.under_bot, Ideal.ramificationIdx'_bot, zero_ne_one] at h
    have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
    have : 𝔓.IsMaximal := ‹𝔓.IsPrime›.isMaximal hPbot
    have : (𝔓.under (𝓞 K)).IsMaximal :=
      (inferInstance : (𝔓.under (𝓞 K)).IsPrime).isMaximal hpbot
    have : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
    have : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
      Ideal.ramificationIdx_eq_one_iff.mp
        ((Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 hpbot).symm.trans h)
    letI : FaithfulSMul Gal(L/K) (𝓞 L) := IsGaloisGroup.faithful (𝓞 K)
    have heq : σ = arithFrobAt (𝓞 K) Gal(L/K) 𝔓 :=
      MulSemiringAction.toAlgHom_injective (𝓞 K) (𝓞 L) <|
        AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hσ
          (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) 𝔓.primeCompl_le_nonZeroDivisors
    rw [heq]
    let : Field (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Ideal.Quotient.field _
    let : Field (𝓞 L ⧸ 𝔓) := Ideal.Quotient.field _
    have : Finite (𝓞 K ⧸ 𝔓.under (𝓞 K)) :=
      Ideal.finiteQuotientOfFreeOfNeBot (𝔓.under (𝓞 K)) hpbot
    have : Algebra.IsSeparable (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) :=
      IsGalois.to_isSeparable
    have : Algebra.IsAlgebraic (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) :=
      Algebra.IsAlgebraic.of_finite _ _
    let : Fintype (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Fintype.ofFinite _
    set g₀ : MulAction.stabilizer Gal(L/K) 𝔓 :=
      ⟨arithFrobAt (𝓞 K) Gal(L/K) 𝔓,
        IsArithFrobAt.arithFrobAt_mem_stabilizer (𝓞 K) Gal(L/K) 𝔓⟩ with hg₀
    have hres :
        Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K) g₀ =
          FiniteField.frobeniusAlgEquivOfAlgebraic
            (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
      ext x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [hg₀, Ideal.Quotient.stabilizerHom_apply,
        FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ← Nat.card_eq_fintype_card]
      exact (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓).mk_apply b
    have hinj :
        Function.Injective (Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K)) := by
      rw [← MonoidHom.ker_eq_bot_iff, Ideal.Quotient.ker_stabilizerHom]
      show (Ideal.inertia Gal(L/K) 𝔓).subgroupOf (MulAction.stabilizer Gal(L/K) 𝔓) = ⊥
      rw [show Ideal.inertia Gal(L/K) 𝔓 = ⊥ from by
        rw [Subgroup.eq_bot_iff_card,
          Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) (𝔓.under (𝓞 K)) 𝔓,
          Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 Gal(L/K),
          ← Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 hpbot]
        exact h,
        Subgroup.bot_subgroupOf]
    calc
      orderOf (arithFrobAt (𝓞 K) Gal(L/K) 𝔓) = orderOf g₀ := by
        rw [hg₀, Subgroup.orderOf_mk]
      _ = orderOf (Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K) g₀) :=
          (orderOf_injective _ hinj g₀).symm
      _ = orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic
            (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓)) := by rw [hres]
      _ = Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) :=
          FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic _ _
  have hinertK : (𝔓.under (𝓞 K)).inertiaDeg' 𝔓 = orderOf σ := by
    rw [Ideal.inertiaDeg'_algebraMap, horder]
  have hcardstab' : Nat.card (MulAction.stabilizer Gal(L/K) 𝔓) = orderOf σ := by
    rw [Ideal.card_stabilizer_eq (𝔓.under (𝓞 K)) 𝔓,
      Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 Gal(L/K),
      ← Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 hpbot, hraK, one_mul,
      Ideal.inertiaDegIn_eq_inertiaDeg (𝔓.under (𝓞 K)) 𝔓 Gal(L/K),
      ← Ideal.inertiaDeg'_eq_inertiaDeg (𝔓.under (𝓞 K)) 𝔓, hinertK]
  have hstab : Subgroup.zpowers σ = MulAction.stabilizer Gal(L/K) 𝔓 :=
    Subgroup.eq_of_le_of_card_ge (by rwa [Subgroup.zpowers_le])
      (by rw [Nat.card_zpowers, hcardstab'])
  rw [eq_top_iff]
  intro τ _
  rw [MulAction.mem_stabilizer_iff]
  change τ • 𝔓 = 𝔓
  have hmemfix : τ.restrictScalars K
      ∈ IntermediateField.fixingSubgroup (IntermediateField.fixedField (Subgroup.zpowers σ)) :=
    fun x ↦ τ.commutes x
  rw [IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers σ)] at hmemfix
  have hstabmem : τ.restrictScalars K ∈ MulAction.stabilizer Gal(L/K) 𝔓 := hstab ▸ hmemfix
  exact MulAction.mem_stabilizer_iff.mp hstabmem

/-- **The fixed-field prime below `𝔓` has degree one over `K`** (Sharifi 7.2.2 p. 143, "`P` has
degree one over `K`"). Continuing from `stabilizer_intermediate_eq_top_of_frobenius`: with
`P = 𝔓 ∩ 𝓞 E`, since `𝔓` is unramified over `K` the ramification index `e(𝔓 ∣ P) = 1`, and the
decomposition group of `𝔓` in `Gal(L/E)` being all of `Gal(L/E)` forces the inertia degree
`f(𝔓 ∣ P) = [L : E] = f`, hence by the tower law `f(P ∣ 𝔭) = f(𝔓 ∣ 𝔭)/f(𝔓 ∣ P) = f/f = 1`.
The residue field of `P` over `K` is therefore trivial, i.e. `N P = N 𝔭`. -/
theorem inertiaDeg_under_E_eq_one_of_frobenius
    (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hunrK : UnramifiedIn K L (𝔓.under (𝓞 K))) (hPK : 𝔓.LiesOver (𝔓.under (𝓞 K)))
    (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓)
    (horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ)))) :
    haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
      (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
    Ideal.ramificationIdx'
        (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) 𝔓 = 1
      ∧ (𝔓.under (𝓞 K)).inertiaDeg'
          (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) = 1
      ∧ Nat.card (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))
            ⧸ 𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
          = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K)) := by
  set E := IntermediateField.fixedField (Subgroup.zpowers σ) with hE
  haveI : IsScalarTower K ↥E L := E.isScalarTower_mid'
  haveI : IsGalois (↥E) L := IsGalois.tower_top_intermediateField _
  have hraK : Ideal.ramificationIdx' (𝔓.under (𝓞 K)) 𝔓 = 1 := by
    have hPbot := Ideal.ne_bot_of_liesOver_of_ne_bot hunrK.1 𝔓
    have hpbot := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
    haveI : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
      hunrK.2 𝔓 (‹𝔓.IsPrime›.isMaximal hPbot) hPK
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 hpbot]
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have hPbot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hunrK.1 𝔓
  have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := (hunrK).1
  haveI : 𝔓.IsMaximal := ‹𝔓.IsPrime›.isMaximal hPbot
  haveI : (𝔓.under (𝓞 K)).IsMaximal :=
    (inferInstance : (𝔓.under (𝓞 K)).IsPrime).isMaximal hpbot
  haveI : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
  haveI hPEp : (𝔓.under (𝓞 ↥E)).IsPrime := inferInstance
  haveI hPK' : 𝔓.LiesOver (𝔓.under (𝓞 K)) := Ideal.over_under (A := 𝓞 K) (P := 𝔓)
  haveI hPEK : (𝔓.under (𝓞 ↥E)).LiesOver (𝔓.under (𝓞 K)) := inferInstance
  haveI hPPE : 𝔓.LiesOver (𝔓.under (𝓞 ↥E)) := Ideal.over_under (A := 𝓞 ↥E) (P := 𝔓)
  have hpEbot : 𝔓.under (𝓞 ↥E) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 ↥E) hPbot
  haveI : (𝔓.under (𝓞 ↥E)).IsMaximal := hPEp.isMaximal hpEbot
  have hraE : Ideal.ramificationIdx' (𝔓.under (𝓞 ↥E)) 𝔓 = 1 := by
    have htower := Ideal.ramificationIdx'_algebra_tower' (𝔓.under (𝓞 K)) (𝔓.under (𝓞 ↥E)) 𝔓
    rw [hraK] at htower
    exact Nat.eq_one_of_mul_eq_one_left htower.symm
  haveI : Algebra.IsSeparable (𝓞 ↥E ⧸ 𝔓.under (𝓞 ↥E)) (𝓞 L ⧸ 𝔓) := by
    letI : Field (𝓞 ↥E ⧸ 𝔓.under (𝓞 ↥E)) := Ideal.Quotient.field _
    letI : Field (𝓞 L ⧸ 𝔓) := Ideal.Quotient.field _
    exact IsGalois.to_isSeparable
  have hstabE : MulAction.stabilizer Gal(L/(↥E)) 𝔓 = ⊤ :=
    stabilizer_intermediate_eq_top_of_frobenius σ 𝔓 hunrK hPK hfrob horderE
  have hcardE : Nat.card (MulAction.stabilizer Gal(L/(↥E)) 𝔓)
      = (𝔓.under (𝓞 ↥E)).ramificationIdxIn (𝓞 L) * (𝔓.under (𝓞 ↥E)).inertiaDegIn (𝓞 L) :=
    Ideal.card_stabilizer_eq (𝔓.under (𝓞 ↥E)) 𝔓
  rw [hstabE, Subgroup.card_top,
    Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓.under (𝓞 ↥E)) 𝔓 Gal(L/(↥E)),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 ↥E)) 𝔓 hpEbot, hraE, one_mul,
    Ideal.inertiaDegIn_eq_inertiaDeg (𝔓.under (𝓞 ↥E)) 𝔓 Gal(L/(↥E)),
    ← Ideal.inertiaDeg'_eq_inertiaDeg (𝔓.under (𝓞 ↥E)) 𝔓,
    Ideal.inertiaDeg'_algebraMap] at hcardE
  have hinertTower : (𝔓.under (𝓞 K)).inertiaDeg' 𝔓
      = (𝔓.under (𝓞 K)).inertiaDeg' (𝔓.under (𝓞 ↥E))
        * (𝔓.under (𝓞 ↥E)).inertiaDeg' 𝔓 :=
    Ideal.inertiaDeg'_algebra_tower (𝔓.under (𝓞 K)) (𝔓.under (𝓞 ↥E)) 𝔓
  have horder : orderOf σ =
      Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
    have h : Ideal.ramificationIdx' (𝔓.under (𝓞 K)) 𝔓 = 1 := hraK
    have hσ : IsArithFrobAt (𝓞 K) σ 𝔓 := hfrob
    have hPbot : 𝔓 ≠ ⊥ := by
      rintro rfl
      simp only [Ideal.under_bot, Ideal.ramificationIdx'_bot, zero_ne_one] at h
    have hpbot : 𝔓.under (𝓞 K) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 K) hPbot
    have : 𝔓.IsMaximal := ‹𝔓.IsPrime›.isMaximal hPbot
    have : (𝔓.under (𝓞 K)).IsMaximal :=
      (inferInstance : (𝔓.under (𝓞 K)).IsPrime).isMaximal hpbot
    have : Finite (𝓞 L ⧸ 𝔓) := Ideal.finiteQuotientOfFreeOfNeBot 𝔓 hPbot
    have : Algebra.IsUnramifiedAt (𝓞 K) 𝔓 :=
      Ideal.ramificationIdx_eq_one_iff.mp
        ((Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 hpbot).symm.trans h)
    letI : FaithfulSMul Gal(L/K) (𝓞 L) := IsGaloisGroup.faithful (𝓞 K)
    have heq : σ = arithFrobAt (𝓞 K) Gal(L/K) 𝔓 :=
      MulSemiringAction.toAlgHom_injective (𝓞 K) (𝓞 L) <|
        AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hσ
          (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓) 𝔓.primeCompl_le_nonZeroDivisors
    rw [heq]
    let : Field (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Ideal.Quotient.field _
    let : Field (𝓞 L ⧸ 𝔓) := Ideal.Quotient.field _
    have : Finite (𝓞 K ⧸ 𝔓.under (𝓞 K)) :=
      Ideal.finiteQuotientOfFreeOfNeBot (𝔓.under (𝓞 K)) hpbot
    have : Algebra.IsSeparable (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) :=
      IsGalois.to_isSeparable
    have : Algebra.IsAlgebraic (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) :=
      Algebra.IsAlgebraic.of_finite _ _
    let : Fintype (𝓞 K ⧸ 𝔓.under (𝓞 K)) := Fintype.ofFinite _
    set g₀ : MulAction.stabilizer Gal(L/K) 𝔓 :=
      ⟨arithFrobAt (𝓞 K) Gal(L/K) 𝔓,
        IsArithFrobAt.arithFrobAt_mem_stabilizer (𝓞 K) Gal(L/K) 𝔓⟩ with hg₀
    have hres :
        Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K) g₀ =
          FiniteField.frobeniusAlgEquivOfAlgebraic
            (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) := by
      ext x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [hg₀, Ideal.Quotient.stabilizerHom_apply,
        FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ← Nat.card_eq_fintype_card]
      exact (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) 𝔓).mk_apply b
    have hinj :
        Function.Injective (Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K)) := by
      rw [← MonoidHom.ker_eq_bot_iff, Ideal.Quotient.ker_stabilizerHom]
      show (Ideal.inertia Gal(L/K) 𝔓).subgroupOf (MulAction.stabilizer Gal(L/K) 𝔓) = ⊥
      rw [show Ideal.inertia Gal(L/K) 𝔓 = ⊥ from by
        rw [Subgroup.eq_bot_iff_card,
          Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) (𝔓.under (𝓞 K)) 𝔓,
          Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 Gal(L/K),
          ← Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 hpbot]
        exact h,
        Subgroup.bot_subgroupOf]
    calc
      orderOf (arithFrobAt (𝓞 K) Gal(L/K) 𝔓) = orderOf g₀ := by
        rw [hg₀, Subgroup.orderOf_mk]
      _ = orderOf (Ideal.Quotient.stabilizerHom 𝔓 (𝔓.under (𝓞 K)) Gal(L/K) g₀) :=
          (orderOf_injective _ hinj g₀).symm
      _ = orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic
            (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓)) := by rw [hres]
      _ = Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) :=
          FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic _ _
  have hinertK : (𝔓.under (𝓞 K)).inertiaDeg' 𝔓 = orderOf σ := by
    rw [Ideal.inertiaDeg'_algebraMap, horder]
  have hfPE : (𝔓.under (𝓞 ↥E)).inertiaDeg' 𝔓 = orderOf σ := by
    rw [Ideal.inertiaDeg'_algebraMap, ← hcardE, horderE]
  have hpos : 0 < orderOf σ := orderOf_pos_iff.mpr (isOfFinOrder_of_finite σ)
  have hinertPK : (𝔓.under (𝓞 K)).inertiaDeg' (𝔓.under (𝓞 ↥E)) = 1 := by
    rw [hinertK, hfPE] at hinertTower
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [one_mul]; exact hinertTower.symm)
  refine ⟨hraE, hinertPK, ?_⟩
  have hnormP : Nat.card (𝓞 ↥E ⧸ 𝔓.under (𝓞 ↥E))
      = Nat.card (𝓞 K ⧸ 𝔓.under (𝓞 K)) ^ (𝔓.under (𝓞 K)).inertiaDeg' (𝔓.under (𝓞 ↥E)) := by
    simpa [Submodule.cardQuot_apply, Ideal.absNorm_apply] using
      Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver (𝔓.under (𝓞 ↥E)) (𝔓.under (𝓞 K))
        inferInstance hpbot
  rw [hnormP, hinertPK, pow_one]

/-- **`𝔓` is the unique prime of `𝓞 L` above `𝔓 ∩ 𝓞 E`** (Sharifi 7.2.2 p. 143, "`P` is by
definition inert in `L`"). Since `stabilizer Gal(L/E) 𝔓 = ⊤` and `Gal(L/E)` acts transitively
on the primes above `𝔓 ∩ 𝓞 E`, any prime `𝔔` of `𝓞 L` above `𝔓 ∩ 𝓞 E` equals `𝔓`. -/
theorem eq_of_liesOver_under_E_of_frobenius
    (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    (hunrK : UnramifiedIn K L (𝔓.under (𝓞 K))) (hPK : 𝔓.LiesOver (𝔓.under (𝓞 K)))
    (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓)
    (horderE : orderOf σ = Nat.card Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (𝔔 : Ideal (𝓞 L)) [𝔔.IsPrime]
    (hQ : haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
        (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
      𝔔.LiesOver (𝔓.under (𝓞 ↥(IntermediateField.fixedField (Subgroup.zpowers σ))))) :
    𝔔 = 𝔓 := by
  haveI : IsScalarTower K ↥(IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    (IntermediateField.fixedField (Subgroup.zpowers σ)).isScalarTower_mid'
  haveI : IsGalois (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L :=
    IsGalois.tower_top_intermediateField _
  haveI : IsGaloisGroup Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ))))
      (↥(IntermediateField.fixedField (Subgroup.zpowers σ))) L := IsGaloisGroup.of_isGalois _ L
  set E := IntermediateField.fixedField (Subgroup.zpowers σ) with hE
  haveI := hQ
  haveI : 𝔓.LiesOver (𝔓.under (𝓞 ↥E)) := Ideal.over_under (A := 𝓞 ↥E) (P := 𝔓)
  have hstabE : MulAction.stabilizer Gal(L/(↥E)) 𝔓 = ⊤ :=
    stabilizer_intermediate_eq_top_of_frobenius σ 𝔓 hunrK hPK hfrob horderE
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (𝔓.under (𝓞 ↥E)) 𝔓 𝔔 Gal(L/(↥E))
  rw [← hτ, MulAction.mem_stabilizer_iff.mp (hstabE ▸ Subgroup.mem_top τ)]

end Chebotarev
