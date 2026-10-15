/- GID: D5/S3/ConceptDynamics/Coding/ResetNativeUnitNormalForm
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetNativeUnitNormalForm
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Unique signed time normal forms on the original native group and full history representation. -/
import D5.S3.ConceptDynamics.Coding.ResetIntegralUnits
import D5.S3.ConceptDynamics.Coding.ResetHistoryKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm
open Polynomial ResetSignIntegerCyclic ResetIntegralGluing ResetIntegralUnits
open ResetNativeIntegerChart ResetNumberedHistories ResetNativeIntegralDefect
open ResetStandardBeamGeometry ResetFullStandardBeamRepresentation StandardBeamHomeomorphisms
open ResetHistoryKernel

local instance nativeIntModule (q : ℕ) : Module ℤ (Native q) := AddCommGroup.toIntModule _

/-- An integer-linear chart; the original dimension group acquires no ring structure. -/
def nativeGluing (q : ℕ) (hq : 0 < q) : Native q ≃ₗ[ℤ] Compatible q :=
  (nativeIntEquiv q hq).symm.trans (gluing q).toAddEquiv.toIntLinearEquiv

/-- Literal forward time, sign, scalar and inverse-transition stage orientation. -/
theorem native_gluing (q : ℕ) (hq : 0 < q) :
    (∀ z : QF q, nativeGluing q hq (nativeIntEquiv q hq z) = gluing q z) ∧
    (∀ v : Native q, nativeGluing q hq (resetTheta q v) =
      gluing q (fp q X) * nativeGluing q hq v) ∧
    (∀ v : Native q, nativeGluing q hq
      (InertGroupBlockConjugacy.groupAction (resetMatrix q) (Multiplicative.ofAdd true) v) =
      gluing q (fp q (W q)) * nativeGluing q hq v) ∧
    (∀ z : ℤ, ∀ v : Native q, nativeGluing q hq (z • v) = z • nativeGluing q hq v) ∧
    (∀ n : ℕ, ∀ v : InertGroupBlockConjugacy.VertexModule Sign q,
      nativeGluing q hq (ResetNativeIntegerChart.nativeStage q n v) =
        gluing q (ringEquiv q (pp q
          (D5.S1.Recurrence.FiniteCompanionCyclicModule.coordinatePolynomial resetLabel q
            ((resetInverse q hq ^ n) v))))) := by
  obtain ⟨hone,hX,hPoly,hScalar,hPol,hStage,hAction,hLabel⟩ := native_presentation q hq
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro z
    change gluing q ((nativeIntEquiv q hq).symm (nativeIntEquiv q hq z)) = _
    rw [LinearEquiv.symm_apply_apply]
  · intro v
    obtain ⟨b,rfl⟩ := (nativeIntEquiv q hq).surjective v
    rw [← hX]
    change gluing q ((nativeIntEquiv q hq).symm (nativeIntEquiv q hq (fp q X * b))) =
      gluing q (fp q X) * gluing q ((nativeIntEquiv q hq).symm (nativeIntEquiv q hq b))
    simp only [LinearEquiv.symm_apply_apply, map_mul]
  · intro v
    obtain ⟨b,rfl⟩ := (nativeIntEquiv q hq).surjective v
    rw [hLabel, ← hPoly]
    change gluing q ((nativeIntEquiv q hq).symm (nativeIntEquiv q hq (fp q (W q) * b))) =
      gluing q (fp q (W q)) * gluing q ((nativeIntEquiv q hq).symm (nativeIntEquiv q hq b))
    simp only [LinearEquiv.symm_apply_apply, map_mul]
  · exact fun z v => (nativeGluing q hq).map_smul z v
  · intro n v
    change gluing q ((nativeIntEquiv q hq).symm (ResetNativeIntegerChart.nativeStage q n v)) = _
    rw [hStage]

private theorem inverse_time (q : ℕ) (A : Native q ≃ₗ[ℤ] Native q)
    (ht : ∀ x, A (resetTheta q x) = resetTheta q (A x)) :
    ∀ x, A.symm (resetTheta q x) = resetTheta q (A.symm x) := by
  intro x
  apply A.injective
  rw [LinearEquiv.apply_symm_apply, ht, LinearEquiv.apply_symm_apply]

/-- The scalar and its inverse are obtained from the actual automorphism and its inverse. -/
def scalarUnit (q : ℕ) (hq : 0 < q) (A : Native q ≃ₗ[ℤ] Native q)
    (ht : ∀ x, A (resetTheta q x) = resetTheta q (A x)) : (QF q)ˣ := by
  let B := centralizingMap q hq A.toLinearMap ht
  let C := centralizingMap q hq A.symm.toLinearMap (inverse_time q A ht)
  have hc : C 1 * B 1 = 1 := by
    rw [← centralizingMap_scalar q hq A.toLinearMap ht (C 1)]
    change (nativeIntEquiv q hq).symm
      (A (nativeIntEquiv q hq ((nativeIntEquiv q hq).symm
        (A.symm (nativeIntEquiv q hq 1))))) = 1
    simp
  exact ⟨B 1, C 1, (mul_comm _ _).trans hc, hc⟩

/-- Units act by integer-linear conjugation through the original native chart. -/
def nativeAction (q : ℕ) (hq : 0 < q) : (QF q)ˣ →* (Native q ≃ₗ[ℤ] Native q) where
  toFun u := (nativeIntEquiv q hq).symm.trans
    ((u.mulLeftLinearEquiv ℤ (QF q)).trans (nativeIntEquiv q hq))
  map_one' := by ext v; simp
  map_mul' u w := by ext v; simp [mul_assoc]

private theorem nativeAction_apply (q : ℕ) (hq : 0 < q) (u : (QF q)ˣ) (v : Native q) :
    nativeAction q hq u v =
      nativeIntEquiv q hq ((u : QF q) * (nativeIntEquiv q hq).symm v) := rfl

private theorem nativeAction_injective (q : ℕ) (hq : 0 < q) :
    Function.Injective (nativeAction q hq) := by
  intro u v h
  apply Units.ext
  have he := congrArg (fun A : Native q ≃ₗ[ℤ] Native q =>
    (nativeIntEquiv q hq).symm (A (nativeIntEquiv q hq 1))) h
  simpa only [nativeAction_apply, LinearEquiv.symm_apply_apply, mul_one] using he

private theorem scalarUnit_action (q : ℕ) (hq : 0 < q) (A : Native q ≃ₗ[ℤ] Native q)
    (ht : ∀ x, A (resetTheta q x) = resetTheta q (A x)) :
    nativeAction q hq (scalarUnit q hq A ht) = A := by
  ext v
  obtain ⟨b,rfl⟩ := (nativeIntEquiv q hq).surjective v
  apply (nativeIntEquiv q hq).symm.injective
  rw [nativeAction_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  have hs := centralizingMap_scalar q hq A.toLinearMap ht b
  exact (mul_comm _ _).trans hs.symm

section UniformNativeTransientExactCheck

open InertGroupBlockConjugacy (groupAction)

variable (q : ℕ) (hq : 0 < q)

-- These are local notation expansions, not new retained named declarations.
-- Native q remains literally DimensionGroup (resetMatrix q).
local notation "signNative" =>
  groupAction (resetMatrix q) (Multiplicative.ofAdd true)
local notation "Kplus" =>
  ((signNative - (LinearMap.id : Module.End ℤ (Native q))).toAddMonoidHom.ker)
local notation "Kminus" =>
  ((signNative + (LinearMap.id : Module.End ℤ (Native q))).toAddMonoidHom.ker)
local notation "Lnative" => (Kplus ⊔ Kminus)
local notation "Qnative" => (Native q ⧸ Lnative)
local notation "kappaNative" =>
  ((commonResidue q).toAddMonoidHom.comp (nativeGluing q hq).toAddMonoidHom)
local notation "nativeGenerator" => nativeIntEquiv q hq (1 : QF q)

-- A clause-complete transient application, including q=1 and ALL A and h.
-- No assumption identifies a surrogate action or assumes an induced map.
private theorem uniformOriginalNativeQuotientExactCheck :
    (∀ v : Native q,
      (v ∈ Kplus ↔ signNative v = v) ∧
      (v ∈ Kminus ↔ signNative v = -v)) ∧
    (Lnative).map (nativeGluing q hq).toAddMonoidHom =
      eigenLattice q 1 ⊔ eigenLattice q (-1) ∧
    (∀ v : Native q, v ∈ Lnative ↔
      ∃ a : Plus q, ∃ b : Minus q,
        (nativeGluing q hq v).val = (2 * a, 2 * b)) ∧
    (∀ v : Native q, v ∈ Lnative ↔
      ∀ t : Plus q × Minus q,
        (nativeGluing q hq v).val * t ∈ (rplus q).pullback (rminus q)) ∧
    Function.Surjective kappaNative ∧
    (kappaNative).ker = Lnative ∧
    (∃ E : Qnative ≃+ Common q,
      (∀ v : Native q, E (QuotientAddGroup.mk' Lnative v) = kappaNative v) ∧
      Nat.card Qnative = 2 ^ q ∧
      (∀ v : Native q, kappaNative (resetTheta q v) =
        (commonTimeUnit q : Common q) * kappaNative v) ∧
      (∀ s : Sign, ∀ v : Native q,
        kappaNative (groupAction (resetMatrix q) s v) = kappaNative v) ∧
      (∀ s : Sign,
        ∃ hs : Lnative ≤ (Lnative).comap
          (groupAction (resetMatrix q) s).toAddMonoidHom,
        QuotientAddGroup.map Lnative Lnative
          (groupAction (resetMatrix q) s).toAddMonoidHom hs =
            AddMonoidHom.id Qnative) ∧
      (∀ (A : Native q ≃ₗ[ℤ] Native q)
          (ht : ∀ v, A (resetTheta q v) = resetTheta q (A v)),
        let cA : Common q := kappaNative (A nativeGenerator)
        IsUnit cA ∧
        (∀ v : Native q, kappaNative (A v) = cA * kappaNative v) ∧
        ∃ dA : AddAut Qnative,
          (∀ v : Native q, dA (QuotientAddGroup.mk' Lnative v) =
            QuotientAddGroup.mk' Lnative (A v)) ∧
          (∀ z : Qnative, E (dA z) = cA * E z) ∧
          ∃ hA : Lnative ≤ (Lnative).comap A.toAddMonoidHom,
            QuotientAddGroup.map Lnative Lnative A.toAddMonoidHom hA =
              dA.toAddMonoidHom) ∧
      (∃ rhoBar : ResetFullAut q →* AddAut Qnative,
        (∀ h : ResetFullAut q, ∀ v : Native q,
          rhoBar h (QuotientAddGroup.mk' Lnative v) =
            QuotientAddGroup.mk' Lnative (rho q hq h v)) ∧
        (∀ h : ResetFullAut q,
          IsUnit (kappaNative (rho q hq h nativeGenerator))) ∧
        (∀ h : ResetFullAut q, ∀ v : Native q,
          kappaNative (rho q hq h v) =
            kappaNative (rho q hq h nativeGenerator) * kappaNative v) ∧
        (∀ h : ResetFullAut q, ∀ z : Qnative,
          E (rhoBar h z) =
            kappaNative (rho q hq h nativeGenerator) * E z) ∧
        (∀ v : Native q, rhoBar (unitShift (ResetGraph q))
          (QuotientAddGroup.mk' Lnative v) =
            QuotientAddGroup.mk' Lnative (resetTheta q v)) ∧
        (∀ z : Qnative, E (rhoBar (unitShift (ResetGraph q)) z) =
          (commonTimeUnit q : Common q) * E z) ∧
        orderOf (rhoBar (unitShift (ResetGraph q))) = orderOf (commonTimeUnit q) ∧
        (q = 1 → orderOf (rhoBar (unitShift (ResetGraph q))) = 1) ∧
        (2 ≤ q → orderOf (rhoBar (unitShift (ResetGraph q))) = q + 1))) := by
  classical
  let e := nativeGluing q hq
  let J := eigenLattice q 1 ⊔ eigenLattice q (-1)
  have hplus (v : Native q) : v ∈ Kplus ↔ signNative v = v := by
    change signNative v - v = 0 ↔ signNative v = v
    exact sub_eq_zero
  have hminus (v : Native q) : v ∈ Kminus ↔ signNative v = -v := by
    change signNative v + v = 0 ↔ signNative v = -v
    exact add_eq_zero_iff_eq_neg
  have hsignChart (v : Native q) :
      e (signNative v) = gluing q (fp q (W q)) * e v :=
    (native_gluing q hq).2.2.1 v
  have hp (v : Native q) : e v ∈ eigenLattice q 1 ↔ v ∈ Kplus := by
    rw [hplus]
    change gluing q (fp q (W q)) * e v = (1 : ℤ) • e v ↔ signNative v = v
    rw [one_smul, ← hsignChart]
    exact e.injective.eq_iff
  have hm (v : Native q) : e v ∈ eigenLattice q (-1) ↔ v ∈ Kminus := by
    rw [hminus]
    change gluing q (fp q (W q)) * e v = (-1 : ℤ) • e v ↔ signNative v = -v
    rw [neg_one_zsmul, ← hsignChart, ← map_neg]
    exact e.injective.eq_iff
  have hpmap : (Kplus).map e.toAddMonoidHom = eigenLattice q 1 := by
    ext z
    change (∃ v ∈ Kplus, e v = z) ↔ z ∈ eigenLattice q 1
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (hp v).mpr hv
    · intro hz
      refine ⟨e.symm z, (hp _).mp ?_, e.apply_symm_apply z⟩
      simpa only [LinearEquiv.apply_symm_apply] using hz
  have hmmap : (Kminus).map e.toAddMonoidHom = eigenLattice q (-1) := by
    ext z
    change (∃ v ∈ Kminus, e v = z) ↔ z ∈ eigenLattice q (-1)
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (hm v).mpr hv
    · intro hz
      refine ⟨e.symm z, (hm _).mp ?_, e.apply_symm_apply z⟩
      simpa only [LinearEquiv.apply_symm_apply] using hz
  have hsum : (Lnative).map e.toAddMonoidHom = J := by
    rw [AddSubgroup.map_sup, hpmap, hmmap]
  have hmem (v : Native q) : e v ∈ J ↔ v ∈ Lnative := by
    rw [← hsum]
    exact AddSubgroup.mem_map_iff_mem e.injective
  have heven (v : Native q) : v ∈ Lnative ↔
      ∃ a : Plus q, ∃ b : Minus q, (e v).val = (2 * a, 2 * b) :=
    (hmem v).symm.trans (eigenlattice_sum_even_product q hq (e v))
  have hconductor (v : Native q) : v ∈ Lnative ↔
      ∀ t : Plus q × Minus q, (e v).val * t ∈ (rplus q).pullback (rminus q) := by
    rw [pullback_conductor_even_product q hq, heven]
    constructor
    · rintro ⟨a, b, hab⟩
      refine ⟨(a, b), ?_⟩
      change (e v).val = (2 * a, 2 * b)
      exact hab
    · rintro ⟨a, ha⟩
      refine ⟨a.1, a.2, ?_⟩
      change (e v).val = (2 * a.1, 2 * a.2) at ha
      exact ha
  have hsurj : Function.Surjective kappaNative :=
    (common_residue_surjective q).comp e.surjective
  have hker : (kappaNative).ker = Lnative := by
    ext v
    change commonResidue q (e v) = 0 ↔ v ∈ Lnative
    change e v ∈ (commonResidue q).toAddMonoidHom.ker ↔ v ∈ Lnative
    rw [common_residue_kernel q hq]
    exact hmem v
  -- Generic transport of the ACTUAL subgroup quotient, followed by the
  -- provisional arithmetic first-isomorphism equivalence. No custom quotient.
  let E : Qnative ≃+ Common q :=
    (QuotientAddGroup.congr Lnative J e.toAddEquiv hsum).trans
      (commonResidueQuotientEquiv q hq)
  have hEmk (v : Native q) :
      E (QuotientAddGroup.mk' Lnative v) = kappaNative v := by
    change commonResidueQuotientEquiv q hq (QuotientAddGroup.mk (e v)) =
      commonResidue q (e v)
    rfl
  have hcard : Nat.card Qnative = 2 ^ q :=
    (Nat.card_congr E.toEquiv).trans (common_residue_cardinality q hq).1
  have hgen : kappaNative nativeGenerator = 1 := by
    change commonResidue q (e (nativeIntEquiv q hq 1)) = 1
    rw [(native_gluing q hq).1, map_one, map_one]
  have hX : commonResidue q (gluing q (fp q X)) = (commonTimeUnit q : Common q) := by
    change commonPolynomial q X = AdjoinRoot.root (reduce (g q))
    change AdjoinRoot.mk _ (reduce X) = AdjoinRoot.root (reduce (g q))
    rw [show reduce X = X by simp [reduce], AdjoinRoot.mk_X]
  have hW : commonResidue q (gluing q (fp q (W q))) = 1 := by
    change rplus q (gluing q (fp q (W q))).val.1 = 1
    rw [congrArg Prod.fst (gluing_generators q).2.1, map_one]
  have htime (v : Native q) : kappaNative (resetTheta q v) =
      (commonTimeUnit q : Common q) * kappaNative v := by
    change commonResidue q (e (resetTheta q v)) = _
    rw [(native_gluing q hq).2.1, map_mul, hX]
    rfl
  have hsign (v : Native q) : kappaNative (signNative v) = kappaNative v := by
    change commonResidue q (e (signNative v)) = _
    rw [hsignChart, map_mul, hW, one_mul]
    rfl
  -- The other element of the ORIGINAL Sign=Multiplicative Bool acts as the
  -- literal identity. This is direct-limit naturality, not an inertness premise.
  have hsignOne (v : Native q) : groupAction (resetMatrix q) (1 : Sign) v = v := by
    obtain ⟨n, x, rfl⟩ := Module.DirectLimit.exists_of v
    simp only [groupAction, InertGroupBlockConjugacy.induced,
      Module.DirectLimit.map_apply_of]
    congr 1
    funext i
    change MonoidAlgebra.single (1 : Sign) (1 : ℤ) * x i = x i
    change (1 : MonoidAlgebra ℤ Sign) * x i = x i
    exact one_mul _
  have hallSign (s : Sign) (v : Native q) :
      kappaNative (groupAction (resetMatrix q) s v) = kappaNative v := by
    cases hb : Multiplicative.toAdd s with
    | false =>
      have hs : s = Multiplicative.ofAdd false := congrArg Multiplicative.ofAdd hb
      rw [hs]
      change kappaNative (groupAction (resetMatrix q) (1 : Sign) v) = kappaNative v
      rw [hsignOne]
    | true =>
      have hs : s = Multiplicative.ofAdd true := congrArg Multiplicative.ofAdd hb
      rw [hs]
      exact hsign v
  have hsignStable (s : Sign) : Lnative ≤ (Lnative).comap
      (groupAction (resetMatrix q) s).toAddMonoidHom := by
    intro v hv
    change groupAction (resetMatrix q) s v ∈ Lnative
    rw [← hker]
    change kappaNative (groupAction (resetMatrix q) s v) = 0
    rw [hallSign]
    change v ∈ (kappaNative).ker
    rw [hker]
    exact hv
  have hsignQuotient (s : Sign) :
      QuotientAddGroup.map Lnative Lnative
        (groupAction (resetMatrix q) s).toAddMonoidHom (hsignStable s) =
          AddMonoidHom.id Qnative := by
    ext z
    refine Quotient.inductionOn' z ?_
    intro v
    apply E.injective
    change E (QuotientAddGroup.mk' Lnative (groupAction (resetMatrix q) s v)) =
      E (QuotientAddGroup.mk' Lnative v)
    rw [hEmk, hEmk, hallSign]
  -- Map EXISTING scalarUnit through the actual arithmetic RingHom. Reuse
  -- scalarUnit_action/nativeAction_apply at their original private owner.
  let residueRing : QF q →+* Common q := (commonResidue q).comp (gluing q).toRingHom
  let cUnit (A : Native q ≃ₗ[ℤ] Native q)
      (ht : ∀ v, A (resetTheta q v) = resetTheta q (A v)) : (Common q)ˣ :=
    Units.map residueRing.toMonoidHom (scalarUnit q hq A ht)
  have hscalar (A : Native q ≃ₗ[ℤ] Native q)
      (ht : ∀ v, A (resetTheta q v) = resetTheta q (A v)) (v : Native q) :
      kappaNative (A v) = (cUnit A ht : Common q) * kappaNative v := by
    have ha := LinearEquiv.congr_fun (scalarUnit_action q hq A ht) v
    rw [← ha, nativeAction_apply]
    change commonResidue q (e (nativeIntEquiv q hq
      ((scalarUnit q hq A ht : QF q) * (nativeIntEquiv q hq).symm v))) = _
    rw [(native_gluing q hq).1, map_mul, map_mul]
    rfl
  have hcval (A : Native q ≃ₗ[ℤ] Native q)
      (ht : ∀ v, A (resetTheta q v) = resetTheta q (A v)) :
      (cUnit A ht : Common q) = kappaNative (A nativeGenerator) := by
    simpa only [hgen, mul_one] using (hscalar A ht nativeGenerator).symm
  have hcunit (A : Native q ≃ₗ[ℤ] Native q)
      (ht : ∀ v, A (resetTheta q v) = resetTheta q (A v)) :
      IsUnit (kappaNative (A nativeGenerator)) := ⟨cUnit A ht, hcval A ht⟩
  have hcscalar (A : Native q ≃ₗ[ℤ] Native q)
      (ht : ∀ v, A (resetTheta q v) = resetTheta q (A v)) (v : Native q) :
      kappaNative (A v) = kappaNative (A nativeGenerator) * kappaNative v := by
    rw [← hcval A ht]
    exact hscalar A ht v
  -- The multiplication representation is transported through the PROVED
  -- quotient equivalence, with no multiplication imposed on Native itself.
  let mu : (Common q)ˣ →* AddAut Qnative :=
    { toFun u := E.trans ((u.mulLeftLinearEquiv ℤ (Common q)).toAddEquiv.trans E.symm)
      map_one' := by
        ext z
        change E.symm ((1 : Common q) * E z) = z
        rw [one_mul, E.symm_apply_apply]
      map_mul' := by
        intro u w
        ext z
        change E.symm (((u * w : (Common q)ˣ) : Common q) * E z) =
          E.symm ((u : Common q) * E (E.symm ((w : Common q) * E z)))
        rw [E.apply_symm_apply, Units.val_mul, mul_assoc] }
  have hmu (u : (Common q)ˣ) (z : Qnative) :
      E (mu u z) = (u : Common q) * E z := E.apply_symm_apply _
  have hmuInjective : Function.Injective mu := by
    intro u w huw
    apply Units.ext
    have heq := congrArg (fun d : AddAut Qnative => E (d (E.symm 1))) huw
    simpa only [hmu, E.apply_symm_apply, mul_one] using heq
  have hdesc (A : Native q ≃ₗ[ℤ] Native q)
      (ht : ∀ v, A (resetTheta q v) = resetTheta q (A v)) (v : Native q) :
      mu (cUnit A ht) (QuotientAddGroup.mk' Lnative v) =
        QuotientAddGroup.mk' Lnative (A v) := by
    apply E.injective
    rw [hmu, hEmk, hEmk]
    exact (hscalar A ht v).symm
  have hstable (A : Native q ≃ₗ[ℤ] Native q)
      (ht : ∀ v, A (resetTheta q v) = resetTheta q (A v)) :
      Lnative ≤ (Lnative).comap A.toAddMonoidHom := by
    intro v hv
    change A v ∈ Lnative
    rw [← hker]
    change kappaNative (A v) = 0
    rw [hscalar A ht v]
    have hv0 : kappaNative v = 0 := by
      change v ∈ (kappaNative).ker
      rwa [hker]
    rw [hv0, mul_zero]
  have hgenericMap (A : Native q ≃ₗ[ℤ] Native q)
      (ht : ∀ v, A (resetTheta q v) = resetTheta q (A v)) :
      QuotientAddGroup.map Lnative Lnative A.toAddMonoidHom (hstable A ht) =
        (mu (cUnit A ht)).toAddMonoidHom := by
    ext z
    refine Quotient.inductionOn' z ?_
    intro v
    exact (hdesc A ht v).symm
  let rhoBar : ResetFullAut q →* AddAut Qnative :=
    { toFun h := mu (cUnit (rho q hq h) (rho_time q hq h))
      map_one' := by
        ext z
        refine Quotient.inductionOn' z ?_
        intro v
        change mu (cUnit (rho q hq 1) (rho_time q hq 1))
          (QuotientAddGroup.mk' Lnative v) = QuotientAddGroup.mk' Lnative v
        rw [hdesc, (rho q hq).map_one]
        rfl
      map_mul' := by
        intro h k
        ext z
        refine Quotient.inductionOn' z ?_
        intro v
        change mu (cUnit (rho q hq (h * k)) (rho_time q hq (h * k)))
          (QuotientAddGroup.mk' Lnative v) =
          mu (cUnit (rho q hq h) (rho_time q hq h))
            (mu (cUnit (rho q hq k) (rho_time q hq k))
              (QuotientAddGroup.mk' Lnative v))
        rw [hdesc, hdesc, hdesc, (rho q hq).map_mul]
        rfl }
  have hrho (h : ResetFullAut q) (v : Native q) :
      rhoBar h (QuotientAddGroup.mk' Lnative v) =
        QuotientAddGroup.mk' Lnative (rho q hq h v) :=
    hdesc (rho q hq h) (rho_time q hq h) v
  have hrhoResidue (h : ResetFullAut q) (z : Qnative) :
      E (rhoBar h z) = kappaNative (rho q hq h nativeGenerator) * E z := by
    change E (mu (cUnit (rho q hq h) (rho_time q hq h)) z) = _
    rw [hmu, hcval]
  have htimeUnit :
      cUnit (rho q hq (unitShift (ResetGraph q)))
        (rho_time q hq (unitShift (ResetGraph q))) = commonTimeUnit q := by
    apply Units.ext
    rw [hcval]
    have ht : rho q hq (unitShift (ResetGraph q)) nativeGenerator =
        resetTheta q nativeGenerator :=
      LinearMap.congr_fun (rho_unitShift q hq) nativeGenerator
    rw [ht, htime, hgen, mul_one]
  have htimeQuotient : rhoBar (unitShift (ResetGraph q)) = mu (commonTimeUnit q) := by
    change mu (cUnit (rho q hq (unitShift (ResetGraph q)))
      (rho_time q hq (unitShift (ResetGraph q)))) = mu (commonTimeUnit q)
    rw [htimeUnit]
  have horder : orderOf (rhoBar (unitShift (ResetGraph q))) =
      orderOf (commonTimeUnit q) := by
    rw [htimeQuotient]
    exact orderOf_injective mu hmuInjective (commonTimeUnit q)
  refine ⟨fun v => ⟨hplus v, hminus v⟩, hsum, heven, hconductor,
    hsurj, hker, E, hEmk, hcard, htime, hallSign,
    (fun s => ⟨hsignStable s, hsignQuotient s⟩), ?_, ?_⟩
  · intro A ht
    dsimp only
    refine ⟨hcunit A ht, hcscalar A ht, mu (cUnit A ht), hdesc A ht, ?_,
      hstable A ht, hgenericMap A ht⟩
    intro z
    rw [hmu, hcval]
  · refine ⟨rhoBar, hrho,
      (fun h => hcunit (rho q hq h) (rho_time q hq h)),
      (fun h => hcscalar (rho q hq h) (rho_time q hq h)),
      hrhoResidue, ?_, ?_, horder, ?_, ?_⟩
    · intro v
      rw [hrho]
      exact congrArg (QuotientAddGroup.mk' Lnative)
        (LinearMap.congr_fun (rho_unitShift q hq) v)
    · intro z
      rw [htimeQuotient, hmu]
    · intro hq1
      calc
        orderOf (rhoBar (unitShift (ResetGraph q))) = orderOf (commonTimeUnit q) := horder
        _ = 1 := by rw [hq1]; exact exact_common_time_order.1
    · intro hq2
      exact horder.trans (exact_common_time_order.2 q hq2)

end UniformNativeTransientExactCheck

abbrev N := Native 2
/-- The actual image of the original unit shift, including its inverse powers. -/
def T : N ≃ₗ[ℤ] N := rho 2 (by omega) (unitShift (ResetGraph 2))
/-- The actual original Sign action, kept as an integer-linear endomorphism. -/
def U : Module.End ℤ N :=
  InertGroupBlockConjugacy.groupAction (resetMatrix 2) (Multiplicative.ofAdd true)

private theorem nativeAction_x : nativeAction 2 (by omega) xUnit = T := by
  ext v
  apply (nativeGluing 2 (by omega)).injective
  rw [nativeAction_apply, (native_gluing 2 (by omega)).1]
  have ht : T v = resetTheta 2 v := LinearMap.congr_fun (rho_unitShift 2 (by omega)) v
  rw [ht, (native_gluing 2 (by omega)).2.1]
  simp only [map_mul]
  rfl

private theorem nativeAction_w (v : N) : nativeAction 2 (by omega) wUnit v = U v := by
  apply (nativeGluing 2 (by omega)).injective
  rw [nativeAction_apply, (native_gluing 2 (by omega)).1]
  change _ = nativeGluing 2 (by omega)
    (InertGroupBlockConjugacy.groupAction (resetMatrix 2) (Multiplicative.ofAdd true) v)
  rw [(native_gluing 2 (by omega)).2.2.1]
  simp only [map_mul]
  rfl

private theorem nativeAction_neg (v : N) : nativeAction 2 (by omega) (-1) v = -v := by
  rw [nativeAction_apply]
  simp

private theorem normal_action (n : ℤ) (a b : Fin 2) (v : N) :
    nativeAction 2 (by omega) (normal n a b) v =
      ((-1 : ℤ) ^ a.val) • ((U ^ b.val) ((T ^ n) v)) := by
  simp only [normal, map_mul, map_pow, map_zpow, nativeAction_x,
    LinearEquiv.mul_apply]
  fin_cases a <;> fin_cases b <;>
    simp [LinearEquiv.mul_apply, nativeAction_w, nativeAction_neg]

private theorem centralizer_form (A : N ≃ₗ[ℤ] N)
    (ht : ∀ v, A (resetTheta 2 v) = resetTheta 2 (A v)) :
    ∃! p : ℤ × Fin 2 × Fin 2, ∀ v : N,
      A v = ((-1 : ℤ) ^ p.2.1.val) • ((U ^ p.2.2.val) ((T ^ p.1) v)) := by
  let u := scalarUnit 2 (by omega) A ht
  obtain ⟨p,hp,huniq⟩ := unit_normal_form u
  have hu : nativeAction 2 (by omega) u = A := scalarUnit_action 2 (by omega) A ht
  refine ⟨p,?_,?_⟩
  · intro v
    rw [← hu, hp, normal_action]
  · intro r hr
    apply huniq
    apply nativeAction_injective 2 (by omega)
    rw [hu]
    ext v
    rw [normal_action]
    exact hr v

/-- All native centralizing automorphisms and every value of the original full-history action. -/
theorem native_normal_forms :
    (∀ A : N ≃ₗ[ℤ] N, (∀ v, A (resetTheta 2 v) = resetTheta 2 (A v)) →
      ∃! p : ℤ × Fin 2 × Fin 2, ∀ v : N,
        A v = ((-1 : ℤ) ^ p.2.1.val) • ((U ^ p.2.2.val) ((T ^ p.1) v))) ∧
    (∀ h : ResetFullAut 2, ∃! p : ℤ × Fin 2 × Fin 2, ∀ v : N,
      rho 2 (by omega) h v =
        ((-1 : ℤ) ^ p.2.1.val) • ((U ^ p.2.2.val) ((T ^ p.1) v))) := by
  exact ⟨centralizer_form, fun h => centralizer_form (rho 2 (by omega) h)
    (rho_time 2 (by omega) h)⟩

end D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm
