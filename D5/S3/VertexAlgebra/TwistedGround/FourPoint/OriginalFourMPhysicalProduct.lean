/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalProduct
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite labelled rank-24 Gaussian products on common physical coordinates. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance

/-! Physical chart products with independently marked oscillator coordinates. -/

set_option autoImplicit false

noncomputable section
open Complex Filter
open scoped Topology BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMPhysicalProduct

open LatticeGeneratingFieldLocality (LatticeData)
open OriginalFourMActualChart (Chart Puncture parameter periodRoot)
open OriginalFourMSignedOverlap (legSign signedHalfSource chartCovariance)
open OriginalFourMOccupationTransport (flags physicalSource signed_physical_source_transport)
open OriginalFourMPhysicalCovariance (physicalCovariance signed_physical_covariance_transport)
open private rawLocal halfJacobian chartScale chartDifference from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChartProduct
open private rawLocal_analytic from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccupationTransport
open private chosenChartSource from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSignedOverlap

open OriginalFourMChartProduct (Sample chartProduct)
open OriginalFourMShiftedTheta (chargeTheta)
open LatticeDiscriminantTheta (gramReal)
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge)
open OriginalFourMChargeCoset (fourierSign quadraticSign)
open private pulledCovariance nativeCovariance pulledDifferential differential
  gaussianExponent sourceVector chartTau chartPeriod thetaSource from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChartProduct
open private jac relative physicalDiscrepancy slotCorrection from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance

private def nativeSample (D : LatticeData) (x : ℝ) (i : Puncture)
    (colour : Fin D.rank) (u : ℂ) : Sample D :=
  ⟨(flags .A i).1, (flags .A i).2, rawLocal .A x i u ^ (1 / 2 : ℂ), colour⟩

private theorem nativeSample_sq (D : LatticeData) (x : ℝ) (i : Puncture)
    (colour : Fin D.rank) (u : ℂ) : (nativeSample D x i colour u).q ^ 2 = rawLocal .A x i u := by
  unfold nativeSample
  dsimp only
  rw [← Complex.cpow_mul_nat]
  norm_num

/-- The period-normalized target product in physical coordinates using
that chart's own signed normal covariance and original charge sector. -/
def physicalProduct (D : LatticeData) (hu : IsUnit D.G.det) {X : Type*} [Fintype X]
    (slot : X → Puncture) (colour : X → Fin D.rank) (upperA : Bool) (x : ℝ)
    (c : Chart) (a : ModTwoCharge D) (u weights : X → ℂ) : ℂ :=
  let s := fun i => nativeSample D x (slot i) (colour i) (u i)
  let K := fun i j => relative c (slot i) * relative c (slot j) *
    physicalCovariance upperA c x (slot i) (slot j) (u i) (u j)
  let M := sourceVector D s weights
    (fun i => relative c (slot i) * physicalSource c x (slot i) (u i))
  let P := chartPeriod upperA c x
  (P ^ (12 : ℕ))⁻¹ * Complex.exp (gaussianExponent D s weights K) *
    chargeTheta D hu a (chartTau upperA c x) (thetaSource D P M)

private theorem native_source_entries (D : LatticeData)
    {X : Type*} [Finite X] (slot : X → Puncture) (colour : X → Fin D.rank)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    {w : ℂ} (hwA : w ^ 2 = parameter .A (x : ℂ))
    (hr : ‖parameter .A (x : ℂ)‖ < 1) : ∀ᶠ u : X → ℂ in 𝓝 0, ∀ i : X,
      differential D w (nativeSample D x (slot i) (colour i) (u i)) /
          jac .A x (slot i) (u i) = physicalSource .A x (slot i) (u i) := by
  apply Filter.eventually_all.mpr
  intro i
  let e := (flags .A (slot i)).2
  have hsource := OriginalFourMSignedOverlap.chosen_chart_source_eq_native hx hx1 .A
    (Or.inl rfl) e hr
  have ht : ContinuousAt (fun u : X → ℂ => rawLocal .A x (slot i) (u i)) 0 := by
    apply (rawLocal_analytic hx hx1 .A (slot i)).continuousAt.comp_of_eq
      (continuous_apply i).continuousAt
    rfl
  have hsource' : ∀ᶠ u : X → ℂ in 𝓝 0,
      chosenChartSource .A x e (rawLocal .A x (slot i) (u i)) =
      OriginalGaussianExternalGenerators.sourceMode e
        (rawLocal .A x (slot i) (u i)) (parameter .A x) :=
    hsource.comp_tendsto (by
      simpa only [Pi.zero_apply, rawLocal, zero_div] using ht.tendsto)
  filter_upwards [hsource'] with u hu'
  rw [differential, signedHalfSource, nativeSample_sq, hwA, physicalSource, jac]
  change legSign (flags .A (slot i)).1 *
    OriginalGaussianExternalGenerators.sourceMode e
      (rawLocal .A x (slot i) (u i)) (parameter .A x) / _ = _
  rw [← hu']

private theorem native_covariance_entries (D : LatticeData) (upperA : Bool)
    {X : Type*} [Finite X] (slot : X → Puncture) (colour : X → Fin D.rank)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    {w : ℂ} (hwA : w ^ 2 = parameter .A (x : ℂ))
    (hr : ‖parameter .A (x : ℂ)‖ < 1) : ∀ᶠ u : X → ℂ in 𝓝 0, ∀ i j : X,
      nativeCovariance D (fun k => nativeSample D x (slot k) (colour k) (u k)) w i j =
        chartCovariance upperA .A x (flags .A (slot i)).1 (flags .A (slot j)).1
          (flags .A (slot i)).2 (flags .A (slot j)).2
          (rawLocal .A x (slot i) (u i)) (rawLocal .A x (slot j) (u j)) := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  have hc := OriginalFourMSignedOverlap.chart_covariance_eq_native hx hx1 upperA .A
    (Or.inl rfl) (flags .A (slot i)).1 (flags .A (slot j)).1
    (flags .A (slot i)).2 (flags .A (slot j)).2 hr
  have ht (i : X) : ContinuousAt (fun u : X → ℂ => rawLocal .A x (slot i) (u i)) 0 :=
    (rawLocal_analytic hx hx1 .A (slot i)).continuousAt.comp_of_eq
      (continuous_apply i).continuousAt rfl
  have h₀ (i : X) : rawLocal .A x (slot i) ((0 : X → ℂ) i) = 0 := by simp [rawLocal]
  have hpair : Tendsto (fun u : X → ℂ =>
      (rawLocal .A x (slot i) (u i), rawLocal .A x (slot j) (u j))) (𝓝 0) (𝓝 (0, 0)) := by
    simpa only [h₀] using ((ht i).prodMk (ht j)).tendsto
  have h := hc.symm.comp_tendsto hpair
  filter_upwards [h] with u hu'
  unfold nativeCovariance
  dsimp only
  rw [nativeSample_sq, nativeSample_sq, hwA]
  exact hu'

private theorem physical_cov_from_entries (D : LatticeData) {X : Type*} (s : X → Sample D)
    (i j : X) (upperA : Bool) (c : Chart) (x : ℝ) (w : ℂ)
    (I J : Puncture) (u v : ℂ)
    (hC : nativeCovariance D s w i j =
      chartCovariance upperA .A x (flags .A I).1 (flags .A J).1 (flags .A I).2 (flags .A J).2
        (rawLocal .A x I u) (rawLocal .A x J v))
    (hI : differential D w (s i) / jac .A x I u = physicalSource .A x I u)
    (hJ : differential D w (s j) / jac .A x J v = physicalSource .A x J v)
    (hK : physicalCovariance upperA .A x I J u v - physicalDiscrepancy upperA c x I J u v =
      relative c I * relative c J * physicalCovariance upperA c x I J u v) :
    (pulledCovariance D s upperA c x w i j - slotCorrection .A x I J u v) /
      (jac .A x I u * jac .A x J v) =
    relative c I * relative c J * physicalCovariance upperA c x I J u v := by
  rw [← hK]
  unfold pulledCovariance pulledDifferential physicalCovariance physicalDiscrepancy
  rw [hC, ← hI, ← hJ]
  simp only [div_eq_mul_inv, mul_inv]
  ring

private theorem signed_physical_mean_entries (D : LatticeData)
    {X : Type*} [Finite X] (slot : X → Puncture) (colour : X → Fin D.rank)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    {w : ℂ} (hwA : w ^ 2 = parameter .A (x : ℂ)) (hw : ‖w‖ < 1) (c : Chart) :
    ∀ᶠ u : X → ℂ in 𝓝 0, ∀ i : X,
      pulledDifferential D c x w (nativeSample D x (slot i) (colour i) (u i)) /
        jac .A x (slot i) (u i) =
      relative c (slot i) * physicalSource c x (slot i) (u i) := by
  have hr : ‖parameter .A (x : ℂ)‖ < 1 := by
    rw [← hwA, norm_pow]
    nlinarith [norm_nonneg w]
  have hslot (i : Puncture) :
      (fun u => chartScale c x * physicalSource .A x i u) =ᶠ[𝓝 (0 : ℂ)]
        (fun u => relative c i * physicalSource c x i u) := by
    cases c
    · simp [chartScale, relative]
    · exact (signed_physical_source_transport hx hx1 i).1
    · exact (signed_physical_source_transport hx hx1 i).2
  have hs : ∀ᶠ u : X → ℂ in 𝓝 0, ∀ i : X,
      chartScale c x * physicalSource .A x (slot i) (u i) =
        relative c (slot i) * physicalSource c x (slot i) (u i) :=
    Filter.eventually_all.mpr fun i =>
      (hslot (slot i)).comp_tendsto (by
        have h : Continuous (fun u : X → ℂ => u i) := continuous_apply i
        exact (h.continuousAt (x := 0)).tendsto)
  filter_upwards [native_source_entries D slot colour hx hx1 hwA hr, hs] with u hsu hS
  intro i
  rw [pulledDifferential, mul_div_assoc, hsu i]
  exact hS i

private theorem signed_physical_cov_entries (D : LatticeData) (hu : IsUnit D.G.det)
    {X : Type*} [Finite X] (slot : X → Puncture) (colour : X → Fin D.rank)
    (upperA : Bool) {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    {w : ℂ} (hwA : w ^ 2 = parameter .A (x : ℂ)) (hw : ‖w‖ < 1) (c : Chart) :
    ∀ᶠ u : X → ℂ in 𝓝 0, ∀ i j : X,
      (pulledCovariance D (fun k => nativeSample D x (slot k) (colour k) (u k)) upperA c x w i j -
        slotCorrection .A x (slot i) (slot j) (u i) (u j)) /
          (jac .A x (slot i) (u i) * jac .A x (slot j) (u j)) =
        relative c (slot i) * relative c (slot j) *
          physicalCovariance upperA c x (slot i) (slot j) (u i) (u j) := by
  have hr : ‖parameter .A (x : ℂ)‖ < 1 := by
    rw [← hwA, norm_pow]
    nlinarith [norm_nonneg w]
  let U : Filter (X → ℂ) := 𝓝 0
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  let pair : (X → ℂ) → ℂ × ℂ := fun u => (u i, u j)
  have hc : Continuous pair := (continuous_apply i).prodMk (continuous_apply j)
  have ht : Tendsto pair U (𝓝 (0, 0)) := (hc.continuousAt (x := 0)).tendsto
  have hcov := signed_physical_covariance_transport D hu upperA hx hx1 c (slot i) (slot j)
  have hb := hcov.comp_tendsto ht
  have hs := native_source_entries D slot colour hx hx1 hwA hr
  have hC := native_covariance_entries D upperA slot colour hx hx1 hwA hr
  filter_upwards [hs, hC, hb] with u hsu hCu hKu
  exact physical_cov_from_entries D (fun k => nativeSample D x (slot k) (colour k) (u k))
    i j upperA c x w (slot i) (slot j) (u i) (u j) (hCu i j) (hsu i) (hsu j) hKu

private theorem physical_product_binding (D : LatticeData) (hu : IsUnit D.G.det)
    {X : Type*} [Fintype X] (slot : X → Puncture) (colour : X → Fin D.rank)
    (upperA : Bool) {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    {w : ℂ} (hwA : w ^ 2 = parameter .A (x : ℂ)) (hw : ‖w‖ < 1) (c : Chart) :
    ∀ᶠ u : X → ℂ in 𝓝 0,
      let s := fun i => nativeSample D x (slot i) (colour i) (u i)
      let J := fun i => jac .A x (slot i) (u i)
      ∀ weights : X → ℂ, ∀ a : ModTwoCharge D,
        let weightsA := fun i => weights i / J i
        let correction := gaussianExponent D s weightsA
          (fun i j => slotCorrection .A x (slot i) (slot j) (u i) (u j))
        physicalProduct D hu slot colour upperA x c a u weights =
          Complex.exp (-correction) * chartProduct D hu s weightsA upperA x w c a := by
  filter_upwards [signed_physical_mean_entries D slot colour hx hx1 hwA hw c,
    signed_physical_cov_entries D hu slot colour upperA hx hx1 hwA hw c] with u hM hK
  dsimp only
  intro weights a
  let s := fun i => nativeSample D x (slot i) (colour i) (u i)
  let J := fun i => jac .A x (slot i) (u i)
  let wA := fun i => weights i / J i
  let R := fun i j => slotCorrection .A x (slot i) (slot j) (u i) (u j)
  let K := pulledCovariance D s upperA c x w
  let M := fun i => pulledDifferential D c x w (s i)
  let KP := fun i j => relative c (slot i) * relative c (slot j) *
    physicalCovariance upperA c x (slot i) (slot j) (u i) (u j)
  let MP := fun i => relative c (slot i) * physicalSource c x (slot i) (u i)
  have hm : sourceVector D s weights MP = sourceVector D s wA M := by
    funext k
    unfold sourceVector
    apply Finset.sum_congr rfl
    intro i _
    have hs : M i / J i = MP i := hM i
    rw [← hs]
    simp only [wA]
    split <;> ring
  have hk : gaussianExponent D s weights KP =
      gaussianExponent D s wA K - gaussianExponent D s wA R := by
    have he (i j : X) : (K i j - R i j) / (J i * J j) = KP i j := hK i j
    calc
      gaussianExponent D s weights KP = gaussianExponent D s wA (fun i j => K i j - R i j) := by
        unfold gaussianExponent
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [← he]
        simp only [wA, div_eq_mul_inv, mul_inv]
        ring
      _ = _ := by
        simp only [gaussianExponent, mul_sub, Finset.sum_sub_distrib, sub_div]
  unfold physicalProduct chartProduct
  dsimp only
  change _ * Complex.exp (gaussianExponent D s weights KP) * _ = _
  rw [hm, hk, Complex.exp_sub, Complex.exp_neg]
  ring

/-- The finite rank-24 sector identities on the actual physical-coordinate
Gaussian products. Every label has its own coordinate and weight. Coincident
positions and repeated punctures, colours, and oscillator labels are permitted. -/
theorem physical_chart_product (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (hr : D.rank = 24) {X : Type*} [Fintype X]
    (slot : X → Puncture) (colour : X → Fin D.rank) (upperA : Bool)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    {w : ℂ} (hwA : w ^ 2 = parameter .A (x : ℂ)) (hw : ‖w‖ < 1) :
    ∀ᶠ u : X → ℂ in 𝓝 0, ∀ weights : X → ℂ, ∀ a : ModTwoCharge D,
      let f := fun c a => physicalProduct D hu slot colour upperA x c a u weights
      f .D a = ((2 : ℂ) ^ (12 : ℕ))⁻¹ * (∑ b, fourierSign D a b * f .A b) ∧
      f .B a = (periodRoot .A x ^ (12 : ℕ))⁻¹ *
        (((2 : ℂ) ^ (12 : ℕ))⁻¹ * ∑ b, fourierSign D a b * quadraticSign D b * f .A b) := by
  filter_upwards [physical_product_binding D hu slot colour upperA hx hx1 hwA hw .A,
    physical_product_binding D hu slot colour upperA hx hx1 hwA hw .B,
    physical_product_binding D hu slot colour upperA hx hx1 hwA hw .D] with u hA hB hC
  dsimp only at hA hB hC ⊢
  intro weights a
  let s := fun i => nativeSample D x (slot i) (colour i) (u i)
  let W := fun i => weights i / jac .A x (slot i) (u i)
  let F := fun c a => chartProduct D hu s W upperA x w c a
  let correction := gaussianExponent D s W
    (fun i j => slotCorrection .A x (slot i) (slot j) (u i) (u j))
  let T := Complex.exp (-correction)
  have hA' (b : ModTwoCharge D) :
      physicalProduct D hu slot colour upperA x .A b u weights = T * F .A b := hA weights b
  have hB' : physicalProduct D hu slot colour upperA x .B a u weights = T * F .B a := hB weights a
  have hD' : physicalProduct D hu slot colour upperA x .D a u weights = T * F .D a := hC weights a
  obtain ⟨hd, hb⟩ := OriginalFourMChartProduct.native_chart_product D hu hD hr s W upperA hx hx1 w a
  change F .D a = _ at hd
  change F .B a = _ at hb
  have distribute (k : ℂ) (coeff vals : ModTwoCharge D → ℂ) :
      T * (k * ∑ b, coeff b * vals b) = k * ∑ b, coeff b * (T * vals b) := by
    rw [mul_left_comm T k, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    ring
  constructor
  · rw [hD', hd]
    simp only [hA']
    exact distribute _ _ _
  · rw [hB', hb, mul_left_comm T]
    simp only [hA']
    congr 1
    exact distribute _ _ _

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMPhysicalProduct
