/- GID: D5/S3/Entropy/Fusion/GroupQuotientInformationLoss
   generality: G
   mirror-B: D5/B/S3/Entropy/Fusion/GroupQuotientInformationLoss
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A free finite group quotient loses exactly its conditional residual information. -/

/- Library-search audit trail (2026-09-02):
   * Exact repository hits `shannonEntropy`, `conditionalEntropy`, `entropy_chain_rule`,
     `entropy_eq_log_card_iff_uniform`, `pushforward`, and injective pushforward entropy invariance
     are imported and reused below.
   * Exact Mathlib hits `MulAction.orbitRel.Quotient` and
     `MulAction.selfEquivOrbitsQuotientProd'` supply the genuine quotient and the section-dependent
     residual coordinate. No enumerated replacement carrier is introduced.
   * The repository real-valued finite KL chain rule requires strict positivity, which is not a
     source premise. Mathlib's `InformationTheory.klDiv_compProd_eq_add` instead handles arbitrary
     probability measures in `ℝ≥0∞`; the local bridge below only exposes its common-marginal term
     as the finite weighted conditional sum displayed in the source.
-/

import D5.S3.Entropy.EntropyEquality
import D5.S3.Entropy.Forgetting.DeterministicEntropyEquality
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace D5.S3.Entropy.Fusion.GroupQuotientInformationLoss

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.EntropyEquality
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.Forgetting.DeterministicEntropyEquality
open D5.S3.Entropy.MaxEntropy
open InformationTheory MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable local instance orbitQuotientFintype
    {G Y : Type*} [Group G] [MulAction G Y] [Fintype Y] :
    Fintype (MulAction.orbitRel.Quotient G Y) :=
  Fintype.ofFinite _

/-- The real-valued mass function underlying a probability mass function. -/
noncomputable def realMass {X : Type*} (p : PMF X) : X -> Real :=
  fun x => (p x).toReal

/-- Mathlib's unrestricted extended-valued KL divergence specialized to finite PMFs. -/
noncomputable def pmfKLDivergence {X : Type*} [Fintype X] (p q : PMF X) : ENNReal := by
  letI : MeasurableSpace X := ⊤
  exact klDiv p.toMeasure q.toMeasure

private theorem realMass_is_probability {X : Type*} [Fintype X] (p : PMF X) :
    (forall x, 0 <= realMass p x) /\ ∑ x, realMass p x = 1 := by
  constructor
  · intro x
    exact ENNReal.toReal_nonneg
  · simp only [realMass]
    have pmfSum : (∑ x, p x) = 1 := by
      simpa using p.tsum_coe
    calc
      (∑ x, (p x).toReal) = (∑ x, p x).toReal := by
        symm
        exact ENNReal.toReal_sum fun x _ => PMF.apply_ne_top p x
      _ = 1 := by rw [pmfSum]; simp

/-- The first-coordinate marginal of a finite joint PMF. -/
noncomputable def firstMarginalPMF {B K : Type*} (p : PMF (B × K)) : PMF B :=
  p.map Prod.fst

private theorem firstMarginalPMF_apply {B K : Type*} [Fintype B] [Fintype K]
    (p : PMF (B × K)) (b : B) :
    firstMarginalPMF p b = ∑ k, p (b, k) := by
  classical
  rw [firstMarginalPMF, PMF.map_apply, ENNReal.tsum_prod', tsum_fintype]
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ hb'
    simp [Ne.symm hb']
  · simp

private theorem realMass_map {X W : Type*} [Fintype X] [Fintype W]
    (f : X -> W) (p : PMF X) :
    realMass (p.map f) = pushforward f (realMass p) := by
  classical
  funext w
  rw [realMass, PMF.map_apply, tsum_fintype, pushforward]
  calc
    (∑ x, if w = f x then p x else 0).toReal =
        ∑ x, (if w = f x then p x else 0).toReal := by
      exact ENNReal.toReal_sum fun x _ => by
        by_cases hx : w = f x <;> simp [hx, PMF.apply_ne_top p x]
    _ = ∑ x, if f x = w then realMass p x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : f x = w
      · simp [hx, realMass]
      · simp [hx, Ne.symm hx, realMass]

private theorem realMass_firstMarginal
    {B K : Type*} [Fintype B] [Fintype K] (p : PMF (B × K)) :
    marginal (realMass p) = realMass (firstMarginalPMF p) := by
  classical
  funext b
  change (∑ k, (p (b, k)).toReal) = (firstMarginalPMF p b).toReal
  rw [firstMarginalPMF_apply]
  symm
  exact ENNReal.toReal_sum fun k _ => PMF.apply_ne_top p (b, k)

/-- The conditional PMF on a finite fiber. On a zero-mass fiber its value is irrelevant, and the
identity point is chosen as a total default. -/
noncomputable def fiberPMF {B K : Type*} [Fintype B] [Fintype K] [One K]
    (p : PMF (B × K)) (b : B) : PMF K := by
  classical
  by_cases h : firstMarginalPMF p b = 0
  · exact PMF.pure 1
  · let f : K -> ENNReal := fun k => p (b, k)
    have hf0 : ∑' k, f k ≠ 0 := by
      have heq : ∑' k, f k = firstMarginalPMF p b := by
        rw [tsum_fintype, firstMarginalPMF_apply]
      exact heq ▸ h
    have hf_top : ∑' k, f k ≠ ∞ := by
      rw [tsum_fintype]
      exact ENNReal.sum_ne_top.mpr fun k _ => PMF.apply_ne_top p (b, k)
    exact PMF.normalize f hf0 hf_top

private theorem fiberPMF_apply_of_marginal_ne_zero
    {B K : Type*} [Fintype B] [Fintype K] [One K]
    (p : PMF (B × K)) (b : B) (h : firstMarginalPMF p b ≠ 0) (k : K) :
    fiberPMF p b k = p (b, k) * (firstMarginalPMF p b)⁻¹ := by
  classical
  simp only [fiberPMF, dif_neg h, PMF.normalize_apply]
  rw [tsum_fintype, ← firstMarginalPMF_apply]

/-- A family of PMFs regarded as a Markov kernel on discrete finite spaces. -/
noncomputable def pmfKernel {B K : Type*} [MeasurableSpace B]
    [Countable B] [MeasurableSingletonClass B] [MeasurableSpace K]
    (k : B -> PMF K) : Kernel B K :=
  Kernel.ofFunOfCountable fun b => (k b).toMeasure

private theorem pmfKernel_apply
    {B K : Type*} [MeasurableSpace B] [Countable B]
    [MeasurableSingletonClass B] [MeasurableSpace K]
    (k : B -> PMF K) (b : B) :
    pmfKernel k b = (k b).toMeasure := rfl

private instance pmfKernel_isMarkov {B K : Type*} [MeasurableSpace B]
    [Countable B] [MeasurableSingletonClass B] [MeasurableSpace K]
    (k : B -> PMF K) : IsMarkovKernel (pmfKernel k) :=
  ⟨fun b => by
    change IsProbabilityMeasure (k b).toMeasure
    infer_instance⟩

private theorem pmf_compProd_fiber_eq
    {B K : Type*} [Fintype B] [Fintype K] [One K]
    (p : PMF (B × K)) :
    letI : MeasurableSpace B := ⊤
    letI : MeasurableSpace K := ⊤
    p.toMeasure =
      (firstMarginalPMF p).toMeasure ⊗ₘ pmfKernel (fiberPMF p) := by
  classical
  letI : MeasurableSpace B := ⊤
  letI : MeasurableSpace K := ⊤
  apply Measure.ext_of_singleton
  rintro ⟨b, k⟩
  rw [PMF.toMeasure_apply_singleton p (b, k) (MeasurableSet.singleton _)]
  have hsingleton : ({(b, k)} : Set (B × K)) = {b} ×ˢ {k} := by
    ext z
    simp [Prod.ext_iff]
  rw [hsingleton]
  rw [Measure.compProd_apply_prod (MeasurableSet.singleton b) (MeasurableSet.singleton k)]
  rw [MeasureTheory.lintegral_singleton]
  change p (b, k) =
    (fiberPMF p b).toMeasure {k} * (firstMarginalPMF p).toMeasure {b}
  rw [PMF.toMeasure_apply_singleton (fiberPMF p b) k (MeasurableSet.singleton k)]
  rw [PMF.toMeasure_apply_singleton (firstMarginalPMF p) b (MeasurableSet.singleton b)]
  by_cases hb : firstMarginalPMF p b = 0
  · have hpk : p (b, k) = 0 := by
      apply le_antisymm
      · rw [firstMarginalPMF_apply] at hb
        exact (Finset.single_le_sum (fun k' _ => bot_le) (Finset.mem_univ k)).trans_eq hb
      · exact bot_le
    simp [hb, hpk]
  · rw [fiberPMF_apply_of_marginal_ne_zero p b hb k]
    exact (ENNReal.inv_mul_cancel_right hb (PMF.apply_ne_top _ _)).symm

private theorem klDiv_compProd_same_marginal_eq_sum
    {B K : Type*} [Fintype B]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace K] [MeasurableSpace.CountableOrCountablyGenerated B K]
    (mu : Measure B) [IsFiniteMeasure mu]
    (kappa eta : Kernel B K) [IsMarkovKernel kappa] [IsMarkovKernel eta] :
    klDiv (mu ⊗ₘ kappa) (mu ⊗ₘ eta) =
      ∑ b, mu {b} * klDiv (kappa b) (eta b) := by
  classical
  by_cases hac : mu ⊗ₘ kappa ≪ mu ⊗ₘ eta
  · have hkernel : ∀ᵐ b ∂mu, kappa b ≪ eta b :=
      Measure.absolutelyContinuous_compProd_right_iff.mp hac
    have hk_eq : kappa =ᵐ[mu] eta.withDensity (Kernel.rnDeriv kappa eta) := by
      filter_upwards [hkernel] with b hb
      exact (Kernel.withDensity_rnDeriv_eq hb).symm
    have hmeasure :
        mu ⊗ₘ kappa = (mu ⊗ₘ eta).withDensity
          (fun z => Kernel.rnDeriv kappa eta z.1 z.2) := by
      calc
        mu ⊗ₘ kappa = mu ⊗ₘ eta.withDensity (Kernel.rnDeriv kappa eta) :=
          Measure.compProd_congr hk_eq
        _ = (mu ⊗ₘ eta).withDensity
              (fun z => Kernel.rnDeriv kappa eta z.1 z.2) := by
          rw [Measure.compProd_withDensity]
          exact Kernel.measurable_rnDeriv kappa eta
    have hrn :
        (mu ⊗ₘ kappa).rnDeriv (mu ⊗ₘ eta) =ᵐ[mu ⊗ₘ eta]
          (fun z => Kernel.rnDeriv kappa eta z.1 z.2) := by
      rw [hmeasure]
      exact Measure.rnDeriv_withDensity _ (Kernel.measurable_rnDeriv kappa eta)
    rw [klDiv_eq_lintegral_klFun_of_ac hac]
    calc
      (∫⁻ z, ENNReal.ofReal
          (klFun (((mu ⊗ₘ kappa).rnDeriv (mu ⊗ₘ eta) z).toReal)) ∂(mu ⊗ₘ eta)) =
          ∫⁻ z, ENNReal.ofReal
            (klFun ((Kernel.rnDeriv kappa eta z.1 z.2).toReal)) ∂(mu ⊗ₘ eta) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hrn] with z hz
        rw [hz]
      _ = ∫⁻ b, ∫⁻ k, ENNReal.ofReal
            (klFun ((Kernel.rnDeriv kappa eta b k).toReal)) ∂(eta b) ∂mu := by
        rw [Measure.lintegral_compProd]
        fun_prop
      _ = ∫⁻ b, klDiv (kappa b) (eta b) ∂mu := by
        refine lintegral_congr_ae ?_
        filter_upwards [hkernel] with b hb
        rw [klDiv_eq_lintegral_klFun_of_ac hb]
        refine lintegral_congr_ae ?_
        filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure
          (κ := kappa) (η := eta) (a := b)] with k hk
        rw [hk]
      _ = ∑ b, mu {b} * klDiv (kappa b) (eta b) := by
        rw [lintegral_fintype]
        exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  · rw [klDiv_of_not_ac hac]
    have hnot : ¬ ∀ᵐ b ∂mu, kappa b ≪ eta b := by
      intro h
      exact hac (Measure.absolutelyContinuous_compProd_right_iff.mpr h)
    rw [MeasureTheory.ae_iff_of_countable] at hnot
    push Not at hnot
    rcases hnot with ⟨b, hmu, hb⟩
    symm
    apply (ENNReal.sum_eq_top).2
    refine ⟨b, Finset.mem_univ b, ?_⟩
    rw [klDiv_of_not_ac hb, ENNReal.mul_top]
    exact hmu

private theorem klDiv_map_equiv
    {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]
    (e : X ≃ W) (hme : Measurable e) (hme_inv : Measurable e.symm)
    (p q : PMF X) :
    klDiv (p.map e).toMeasure (q.map e).toMeasure = klDiv p.toMeasure q.toMeasure := by
  rw [← PMF.toMeasure_map (f := e) p hme, ← PMF.toMeasure_map (f := e) q hme]
  apply le_antisymm
  · exact klDiv_map_le p.toMeasure q.toMeasure hme
  · calc
      klDiv p.toMeasure q.toMeasure =
          klDiv ((p.toMeasure.map e).map e.symm) ((q.toMeasure.map e).map e.symm) := by
        simp [Measure.map_map hme_inv hme]
      _ <= klDiv (p.toMeasure.map e) (q.toMeasure.map e) :=
        klDiv_map_le _ _ hme_inv

private theorem conditional_entropy_eq_log_card_only_if_uniform
    {B K : Type*} [Fintype B] [Fintype K] [Nonempty K]
    (p : B × K -> Real)
    (hp : (forall z, 0 <= p z) /\ ∑ z, p z = 1)
    (hmax : conditionalEntropy p = Real.log (Fintype.card K)) :
    forall b, marginal p b ≠ 0 ->
      conditional p b = fun _ => (Fintype.card K : Real)⁻¹ := by
  classical
  let L : Real := Real.log (Fintype.card K)
  have hm_nonneg (b : B) : 0 <= marginal p b := by
    rw [marginal]
    exact Finset.sum_nonneg fun k _ => hp.1 (b, k)
  have hm_total : ∑ b, marginal p b = 1 := by
    rw [show (∑ b, marginal p b) = ∑ z, p z by
      simp only [marginal, Fintype.sum_prod_type]]
    exact hp.2
  have hc_law (b : B) (hb : marginal p b ≠ 0) :
      (forall k, 0 <= conditional p b k) /\ ∑ k, conditional p b k = 1 := by
    constructor
    · intro k
      exact div_nonneg (hp.1 (b, k)) (hm_nonneg b)
    · simp only [conditional]
      rw [← Finset.sum_div, ← marginal, div_self hb]
  have hdef_nonneg (b : B) :
      0 <= marginal p b * (L - shannonEntropy (conditional p b)) := by
    by_cases hb : marginal p b = 0
    · simp [hb]
    · exact mul_nonneg (hm_nonneg b)
        (sub_nonneg.mpr (entropy_le_log_card (conditional p b) (hc_law b hb)))
  have hdef_sum :
      ∑ b, marginal p b * (L - shannonEntropy (conditional p b)) = 0 := by
    calc
      (∑ b, marginal p b * (L - shannonEntropy (conditional p b))) =
          L * ∑ b, marginal p b - conditionalEntropy p := by
        simp_rw [mul_sub]
        rw [conditionalEntropy, Finset.sum_sub_distrib, ← Finset.sum_mul]
        ring
      _ = 0 := by rw [hm_total, hmax]; simp [L]
  have hall_zero :
      forall b, marginal p b * (L - shannonEntropy (conditional p b)) = 0 := by
    intro b
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun b _ => hdef_nonneg b)).mp hdef_sum b (Finset.mem_univ b)
  intro b hb
  have hentropy : shannonEntropy (conditional p b) = L := by
    have := (mul_eq_zero.mp (hall_zero b)).resolve_left hb
    linarith
  exact (entropy_eq_log_card_iff_uniform (conditional p b) (hc_law b hb)).1 (by simpa [L])

/- Source: QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION.md, lines 340-372.
For a finite free `G`-set, a chosen section gives genuine quotient/residual coordinates. The four
conjuncts state, respectively, the Shannon chain rule, its information-loss rearrangement, the
only-if uniform-fiber equality case, and the unrestricted extended-valued KL chain rule. -/
theorem group_quotient_information_loss
    {G Y : Type*} [Fintype G] [Group G] [Fintype Y]
    [MulAction G Y] [IsCancelSMul G Y]
    (representative : MulAction.orbitRel.Quotient G Y -> Y)
    (hsection : Function.LeftInverse Quotient.mk'' representative)
    (Z P Q : PMF Y) :
    let coordinates := MulAction.selfEquivOrbitsQuotientProd' (φ := representative) hsection
      (fun y => IsCancelSMul.stabilizer_eq_bot y)
    let zMass := realMass Z
    let joint := pushforward coordinates zMass
    let quotientLaw := pushforward
      (fun y => (Quotient.mk'' y : MulAction.orbitRel.Quotient G Y)) zMass
    let jointP := P.map coordinates
    let jointQ := Q.map coordinates
    shannonEntropy zMass = shannonEntropy quotientLaw + conditionalEntropy joint /\
      shannonEntropy zMass - shannonEntropy quotientLaw = conditionalEntropy joint /\
      (shannonEntropy zMass - shannonEntropy quotientLaw =
          Real.log (Fintype.card G) ->
        forall b, marginal joint b ≠ 0 ->
          conditional joint b = fun _ => (Fintype.card G : Real)⁻¹) /\
      pmfKLDivergence P Q =
        pmfKLDivergence
          (P.map fun y => (Quotient.mk'' y : MulAction.orbitRel.Quotient G Y))
          (Q.map fun y => (Quotient.mk'' y : MulAction.orbitRel.Quotient G Y)) +
          ∑ b, (firstMarginalPMF jointP b) *
            pmfKLDivergence (fiberPMF jointP b) (fiberPMF jointQ b) := by
  classical
  dsimp only
  let coordinates := MulAction.selfEquivOrbitsQuotientProd' (φ := representative) hsection
    (fun y => IsCancelSMul.stabilizer_eq_bot y)
  let zMass := realMass Z
  let joint := pushforward coordinates zMass
  let quotientMap : Y -> MulAction.orbitRel.Quotient G Y := fun y => Quotient.mk'' y
  let quotientLaw := pushforward quotientMap zMass
  let jointP := P.map coordinates
  let jointQ := Q.map coordinates
  have hz := realMass_is_probability Z
  have hjoint_eq : joint = realMass (Z.map coordinates) := by
    exact (realMass_map coordinates Z).symm
  have hjoint_law : (forall z, 0 <= joint z) /\ ∑ z, joint z = 1 := by
    rw [hjoint_eq]
    exact realMass_is_probability (Z.map coordinates)
  have hjoint_nonnegative : forall z, 0 <= joint z := hjoint_law.1
  have hjointMarginalPMF :
      firstMarginalPMF (Z.map coordinates) = Z.map quotientMap := by
    rw [firstMarginalPMF, PMF.map_comp]
    rfl
  have hmarginal : marginal joint = quotientLaw := by
    rw [hjoint_eq, realMass_firstMarginal, hjointMarginalPMF]
    exact realMass_map quotientMap Z
  have hsource_entropy : shannonEntropy joint = shannonEntropy zMass := by
    exact (pushforward_entropy_eq_iff_injective_on_support zMass coordinates hz).2
      coordinates.injective.injOn
  have hchain := entropy_chain_rule joint hjoint_nonnegative
  rw [hmarginal, hsource_entropy] at hchain
  have hloss : shannonEntropy zMass - shannonEntropy quotientLaw =
      conditionalEntropy joint := by
    linarith
  refine ⟨hchain, hloss, ?_, ?_⟩
  · intro hmaximum
    apply conditional_entropy_eq_log_card_only_if_uniform joint hjoint_law
    rw [← hloss]
    exact hmaximum
  · letI : MeasurableSpace Y := ⊤
    letI : MeasurableSpace (MulAction.orbitRel.Quotient G Y) := ⊤
    letI : MeasurableSpace G := ⊤
    simp only [pmfKLDivergence]
    let pMarginal := firstMarginalPMF jointP
    let qMarginal := firstMarginalPMF jointQ
    let pKernel := pmfKernel (fiberPMF jointP)
    let qKernel := pmfKernel (fiberPMF jointQ)
    have hpFactor : jointP.toMeasure = pMarginal.toMeasure ⊗ₘ pKernel := by
      exact pmf_compProd_fiber_eq jointP
    have hqFactor : jointQ.toMeasure = qMarginal.toMeasure ⊗ₘ qKernel := by
      exact pmf_compProd_fiber_eq jointQ
    have hsum :
        klDiv (pMarginal.toMeasure ⊗ₘ pKernel) (pMarginal.toMeasure ⊗ₘ qKernel) =
          ∑ b, pMarginal b * klDiv (pKernel b) (qKernel b) := by
      simpa [pMarginal, pKernel, qKernel, pmfKernel,
        PMF.toMeasure_apply_singleton] using
        (klDiv_compProd_same_marginal_eq_sum pMarginal.toMeasure pKernel qKernel)
    have hklCoordinate :
        klDiv jointP.toMeasure jointQ.toMeasure =
          klDiv pMarginal.toMeasure qMarginal.toMeasure +
            ∑ b, pMarginal b * klDiv (pKernel b) (qKernel b) := by
      rw [hpFactor, hqFactor, klDiv_compProd_eq_add, hsum]
    have hpMarginal : pMarginal = P.map quotientMap := by
      apply PMF.ext
      intro b
      simp only [pMarginal, firstMarginalPMF, jointP]
      rw [PMF.map_comp]
      rfl
    have hqMarginal : qMarginal = Q.map quotientMap := by
      apply PMF.ext
      intro b
      simp only [qMarginal, firstMarginalPMF, jointQ]
      rw [PMF.map_comp]
      rfl
    have hcoordinateKL :
        klDiv jointP.toMeasure jointQ.toMeasure = klDiv P.toMeasure Q.toMeasure := by
      exact klDiv_map_equiv coordinates (measurable_of_finite coordinates)
        (measurable_of_finite coordinates.symm) P Q
    have hklMarginal :
        klDiv pMarginal.toMeasure qMarginal.toMeasure =
          klDiv (P.map quotientMap).toMeasure (Q.map quotientMap).toMeasure := by
      rw [hpMarginal, hqMarginal]
    rw [hcoordinateKL, hklMarginal] at hklCoordinate
    simpa only [jointP, jointQ, pMarginal, pKernel, qKernel, pmfKernel_apply,
      quotientMap, coordinates] using hklCoordinate

/- Reverse probe A2: the information-loss identity is independently projectable. -/
example
    {G Y : Type*} [Fintype G] [Group G] [Fintype Y]
    [MulAction G Y] [IsCancelSMul G Y]
    (representative : MulAction.orbitRel.Quotient G Y -> Y)
    (hsection : Function.LeftInverse Quotient.mk'' representative)
    (Z P Q : PMF Y) :
    let coordinates := MulAction.selfEquivOrbitsQuotientProd' hsection
      (fun y => IsCancelSMul.stabilizer_eq_bot y)
    let zMass := realMass Z
    let joint := pushforward coordinates zMass
    let quotientLaw := pushforward
      (fun y => (Quotient.mk'' y : MulAction.orbitRel.Quotient G Y)) zMass
    shannonEntropy zMass - shannonEntropy quotientLaw = conditionalEntropy joint := by
  dsimp only
  exact (group_quotient_information_loss representative hsection Z P Q).2.1

/- Reverse probe A3: the only-if uniform-fiber clause is independently projectable. -/
example
    {G Y : Type*} [Fintype G] [Group G] [Fintype Y]
    [MulAction G Y] [IsCancelSMul G Y]
    (representative : MulAction.orbitRel.Quotient G Y -> Y)
    (hsection : Function.LeftInverse Quotient.mk'' representative)
    (Z P Q : PMF Y) :
    let coordinates := MulAction.selfEquivOrbitsQuotientProd' hsection
      (fun y => IsCancelSMul.stabilizer_eq_bot y)
    let zMass := realMass Z
    let joint := pushforward coordinates zMass
    let quotientLaw := pushforward
      (fun y => (Quotient.mk'' y : MulAction.orbitRel.Quotient G Y)) zMass
    shannonEntropy zMass - shannonEntropy quotientLaw =
        Real.log (Fintype.card G) ->
      forall b, marginal joint b ≠ 0 ->
        conditional joint b = fun _ => (Fintype.card G : Real)⁻¹ := by
  dsimp only
  exact (group_quotient_information_loss representative hsection Z P Q).2.2.1

/- Reverse probe A4: the weighted conditional KL identity is independently projectable. -/
example
    {G Y : Type*} [Fintype G] [Group G] [Fintype Y]
    [MulAction G Y] [IsCancelSMul G Y]
    (representative : MulAction.orbitRel.Quotient G Y -> Y)
    (hsection : Function.LeftInverse Quotient.mk'' representative)
    (Z P Q : PMF Y) :
    let coordinates := MulAction.selfEquivOrbitsQuotientProd' hsection
      (fun y => IsCancelSMul.stabilizer_eq_bot y)
    let jointP := P.map coordinates
    let jointQ := Q.map coordinates
    pmfKLDivergence P Q =
      pmfKLDivergence
        (P.map fun y => (Quotient.mk'' y : MulAction.orbitRel.Quotient G Y))
        (Q.map fun y => (Quotient.mk'' y : MulAction.orbitRel.Quotient G Y)) +
        ∑ b, (firstMarginalPMF jointP b) *
          pmfKLDivergence (fiberPMF jointP b) (fiberPMF jointQ b) := by
  dsimp only
  exact (group_quotient_information_loss representative hsection Z P Q).2.2.2

/- Trivialization probe A3: a point mass on a two-point fiber is not conditionally uniform and
therefore cannot attain the conditional entropy `log 2`. -/
example :
    conditionalEntropy
        (fun z : Unit × Fin 2 => if z.2 = 0 then (1 : Real) else 0) ≠
      Real.log (Fintype.card (Fin 2)) := by
  intro hmaximum
  have hp :
      (forall z : Unit × Fin 2,
          0 <= if z.2 = 0 then (1 : Real) else 0) /\
        ∑ z : Unit × Fin 2, (if z.2 = 0 then (1 : Real) else 0) = 1 := by
    constructor
    · intro z
      split <;> norm_num
    · rw [Fintype.sum_prod_type]
      norm_num [Fin.sum_univ_two]
  have huniform := conditional_entropy_eq_log_card_only_if_uniform
    (fun z : Unit × Fin 2 => if z.2 = 0 then (1 : Real) else 0) hp hmaximum
  have hmarginal :
      marginal (fun z : Unit × Fin 2 => if z.2 = 0 then (1 : Real) else 0) () ≠ 0 := by
    norm_num [marginal]
  have hzero := congrFun (huniform () hmarginal) (0 : Fin 2)
  norm_num [conditional, marginal] at hzero

/- Quotient-carrier probe: the genuine orbit quotient distinguishes distinct orbits. -/
example :
    (Quotient.mk'' false : MulAction.orbitRel.Quotient Unit Bool) ≠
      Quotient.mk'' true := by
  intro hcollapse
  have horbit : false ∈ MulAction.orbit Unit true :=
    (Quotient.eq''.mp hcollapse : MulAction.orbitRel Unit Bool false true)
  rcases horbit with ⟨g, hg⟩
  cases g
  simp at hg

/- Reverse probe A1 and definition-self-proof probe: the Shannon chain rule is independently
projectable, but not by definitional reduction. -/
example
    {G Y : Type*} [Fintype G] [Group G] [Fintype Y]
    [MulAction G Y] [IsCancelSMul G Y]
    (representative : MulAction.orbitRel.Quotient G Y -> Y)
    (hsection : Function.LeftInverse Quotient.mk'' representative)
    (Z P Q : PMF Y) :
    let coordinates := MulAction.selfEquivOrbitsQuotientProd' hsection
      (fun y => IsCancelSMul.stabilizer_eq_bot y)
    let zMass := realMass Z
    let joint := pushforward coordinates zMass
    let quotientLaw := pushforward
      (fun y => (Quotient.mk'' y : MulAction.orbitRel.Quotient G Y)) zMass
    shannonEntropy zMass = shannonEntropy quotientLaw + conditionalEntropy joint := by
  fail_if_success rfl
  exact (group_quotient_information_loss representative hsection Z P Q).1

#print axioms group_quotient_information_loss

end D5.S3.Entropy.Fusion.GroupQuotientInformationLoss
