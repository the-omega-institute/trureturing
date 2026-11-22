/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Spatial Wick coefficients of the original four-point charge sums and their overlap. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialTaylor
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalProduct

/-! Spatial Taylor coefficients of the original four-point charge sums. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Topology ContDiff Matrix
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWick

open LatticeGeneratingFieldLocality FourPoint.OriginalFourMActualChart
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge reduceCharge)
open LatticeDiscriminantTheta (gramReal)
open OriginalFourMOccupationTransport (physicalSource physicalSource_analytic)
open OriginalFourMPhysicalCovariance (relative physicalCovariance physicalCovariance_analytic)
open OriginalFourMChartProduct (chartPeriod chartTau chart_charge_data)
open OriginalFourMPhysicalProduct (physicalProduct physical_product_marked_charge_fiber)
open D5.S3.Fourier.MatrixGaussian
  (quadratic exists_quadratic_lower_bound summable_norm_gaussian)

variable {X : Type*} [Fintype X]

private def physicalEntry (D : LatticeData) (upperA : Bool) (c : Chart) (x : ℝ)
    (slot : X → Puncture) (colour : X → Fin D.rank) (i j : X) (u v : ℂ) : ℂ :=
  (D.G (colour i) (colour j) : ℂ) * physicalCovariance upperA c x (slot i) (slot j) u v

private def physicalMean (D : LatticeData) (q : Charge D) (upperA : Bool) (c : Chart) (x : ℝ)
    (slot : X → Puncture) (colour : X → Fin D.rank) (i : X) (u : ℂ) : ℂ :=
  -(bilinear D (unitCharge D (colour i)) q : ℂ) *
    physicalSource c x (slot i) u / chartPeriod upperA c x

private theorem continuousAt_bound {Z : Type*} [TopologicalSpace Z] {z : Z} {f : Z → ℂ}
    (hf : ContinuousAt f z) : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ v in 𝓝 z, ‖f v‖ ≤ M := by
  refine ⟨‖f z‖ + 1, by positivity, ?_⟩
  exact (hf.norm.eventually_lt (continuousAt_const (y := ‖f z‖ + 1)) (by linarith)).mono
    (fun _ h => h.le)

private theorem charge_exponential_majorant {Z : Type*} [TopologicalSpace Z] {z : Z}
    (D : LatticeData) (hD : (gramReal D).PosDef) (τ : ℂ) (hτ : 0 < τ.im)
    (Q : Z → ℂ) (L : Fin D.rank → Z → ℂ)
    (hQ : ContinuousAt Q z) (hL : ∀ j, ContinuousAt (L j) z) :
    ∃ b : Charge D → ℝ, Summable b ∧ ∀ᶠ v in 𝓝 z, ∀ q : Charge D,
      ‖Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (bilinear D q q : ℂ) / 2) *
        Complex.exp (Q v + ∑ j, (q j : ℂ) * L j v)‖ ≤ b q := by
  classical
  obtain ⟨C, hC, hQc⟩ := continuousAt_bound hQ
  choose M hM hMc using fun j => continuousAt_bound (hL j)
  obtain ⟨c, hc, hcoercive⟩ := exists_quadratic_lower_bound (gramReal D) hD
  let d : ℝ := Real.pi * τ.im * c / 4
  have hd : 0 < d := by dsimp [d]; positivity
  let E := Real.exp (C + ∑ j, (M j)^2 / (4 * d))
  let b := fun q : Charge D => ‖Complex.exp
    (-Real.pi * ((τ.im / 4 : ℝ) : ℂ) * (quadratic (gramReal D) (fun j => (q j : ℝ)) : ℂ))‖
  have hb : Summable b := summable_norm_gaussian (gramReal D) hD _ (by
    rw [Complex.ofReal_re]
    positivity)
  refine ⟨fun q => E * b q, hb.mul_left E, ?_⟩
  filter_upwards [hQc, eventually_all.mpr hMc] with v hv hvL
  intro q
  have hEq : (bilinear D q q : ℝ) =
      quadratic (gramReal D) (fun j => (q j : ℝ)) := by
    unfold bilinear quadratic gramReal Matrix.mulVec dotProduct
    push_cast
    simp only [Matrix.map_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hdecay := mul_le_mul_of_nonneg_left (hcoercive (fun j => (q j : ℝ)))
    (show 0 ≤ Real.pi * τ.im / 4 by positivity)
  rw [← hEq] at hdecay
  have hlin (j : Fin D.rank) :
      ((q j : ℂ) * L j v).re ≤ d * (q j : ℝ)^2 + (M j)^2 / (4 * d) := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_intCast]
    refine (mul_le_mul_of_nonneg_left (hvL j) (abs_nonneg (q j : ℝ))).trans ?_
    have hsq := mul_nonneg hd.le (sq_nonneg (|(q j : ℝ)| - M j / (2 * d)))
    have hpoly : d * (|(q j : ℝ)| - M j / (2 * d))^2 =
        d * (q j : ℝ)^2 - |(q j : ℝ)| * M j + (M j)^2 / (4 * d) := by
      rw [sub_sq, sq_abs]
      field_simp
      ring
    rw [hpoly] at hsq
    linarith only [hsq]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hlin j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hqr := (Complex.re_le_norm (Q v)).trans hv
  have hmain : ((Real.pi : ℂ) * Complex.I * τ * (bilinear D q q : ℂ) / 2).re =
      -(Real.pi * τ.im / 2) * (bilinear D q q : ℝ) := by
    rw [show (bilinear D q q : ℂ) = ((bilinear D q q : ℝ) : ℂ) by push_cast; rfl]
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hreal : (∑ j, (q j : ℂ) * L j v).re =
      ∑ j, ((q j : ℂ) * L j v).re :=
    map_sum Complex.reAddGroupHom _ _
  have hhalf : (-Real.pi * ((τ.im / 4 : ℝ) : ℂ) *
      (quadratic (gramReal D) (fun j => (q j : ℝ)) : ℂ)).re =
        -(Real.pi * τ.im / 4) * (bilinear D q q : ℝ) := by
    rw [← hEq, Complex.ofReal_intCast]
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
      mul_zero, zero_mul, sub_zero, add_zero, neg_zero]
    ring
  simp only [norm_mul, Complex.norm_exp, E, b, ← Real.exp_add, hmain, Complex.add_re,
    hreal, hhalf]
  apply Real.exp_le_exp.mpr
  dsimp only [d] at hdecay hsum
  nlinarith only [hdecay, hsum, hqr]

private def markedQuadratic (D : LatticeData) (slot : X → Puncture)
    (colour : X → Fin D.rank) (upperA : Bool) (c : Chart) (x : ℝ) (z : (X ⊕ X) → ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∑ i, ∑ j, physicalEntry D upperA c x slot colour i j
    (z (.inl i)) (z (.inl j)) *
      (relative c (slot i) * z (.inr i)) * (relative c (slot j) * z (.inr j))

private def markedLinear (D : LatticeData) (slot : X → Puncture)
    (colour : X → Fin D.rank) (upperA : Bool) (c : Chart) (x : ℝ)
    (j : Fin D.rank) (z : (X ⊕ X) → ℂ) : ℂ :=
  ∑ i, -(D.G (colour i) j : ℂ) * physicalSource c x (slot i) (z (.inl i)) /
    chartPeriod upperA c x * (relative c (slot i) * z (.inr i))

/-- The summand for one integral charge in the two independent copies of
the mark variables. The finite regular covariance is the physical one. -/
def physicalChargeSummand (D : LatticeData) (slot : X → Puncture)
    (colour : X → Fin D.rank) (upperA : Bool) (c : Chart) (x : ℝ)
    (q : Charge D) (z : (X ⊕ X) → ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x * (bilinear D q q : ℂ) / 2) *
  Complex.exp (markedQuadratic D slot colour upperA c x z +
    ∑ i, physicalMean D q upperA c x slot colour i (z (.inl i)) *
      (relative c (slot i) * z (.inr i)))

private theorem markedLinear_eq (D : LatticeData) (slot : X → Puncture)
    (colour : X → Fin D.rank) (upperA : Bool) (c : Chart) (x : ℝ)
    (q : Charge D) (z : (X ⊕ X) → ℂ) :
    (∑ i, physicalMean D q upperA c x slot colour i (z (.inl i)) *
      (relative c (slot i) * z (.inr i))) =
      ∑ j, (q j : ℂ) * markedLinear D slot colour upperA c x j z := by
  classical
  simp only [markedLinear, physicalMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hrow : bilinear D (unitCharge D (colour i)) q = ∑ j, D.G (colour i) j * q j := by
    unfold bilinear unitCharge
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hrow, Int.cast_sum, ← Finset.sum_neg_distrib, Finset.sum_mul,
    Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

private theorem marked_source_analytic (D : LatticeData) (slot : X → Puncture)
    (colour : X → Fin D.rank) (upperA : Bool) (c : Chart) {x : ℝ}
    (hx : 0 < x) (hx₁ : x < 1) :
    AnalyticAt ℂ (markedQuadratic D slot colour upperA c x) 0 ∧
      ∀ j, AnalyticAt ℂ (markedLinear D slot colour upperA c x j) 0 := by
  have hp (i : X ⊕ X) : AnalyticAt ℂ (fun z : (X ⊕ X) → ℂ => z i) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : X ⊕ X => ℂ) i).analyticAt _
  constructor
  · unfold markedQuadratic
    refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun i _ =>
      Finset.analyticAt_fun_sum _ fun j _ => ?_)
    have hK : AnalyticAt ℂ (fun uv : ℂ × ℂ =>
        physicalEntry D upperA c x slot colour i j uv.1 uv.2) (0, 0) :=
      analyticAt_const.mul (physicalCovariance_analytic upperA hx hx₁ c (slot i) (slot j))
    exact ((hK.comp_of_eq ((hp (.inl i)).prod (hp (.inl j))) rfl).mul
      (analyticAt_const.mul (hp (.inr i)))).mul (analyticAt_const.mul (hp (.inr j)))
  · intro j
    unfold markedLinear
    refine Finset.analyticAt_fun_sum _ fun i _ => ?_
    have h := (physicalSource_analytic hx hx₁ c (slot i)).comp_of_eq (hp (.inl i)) rfl
    exact ((analyticAt_const.mul h).div_const).mul (analyticAt_const.mul (hp (.inr i)))

private theorem physical_charge_summands_normal (D : LatticeData)
    (hD : (gramReal D).PosDef) (slot : X → Puncture) (colour : X → Fin D.rank)
    (upperA : Bool) (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (hτ : 0 < (chartTau upperA c x).im) :
    ∃ (b : Charge D → ℝ) (r : ℝ), Summable b ∧ 0 < r ∧
      (∀ q, AnalyticOnNhd ℂ (physicalChargeSummand D slot colour upperA c x q)
        (Metric.ball 0 r)) ∧
      ∀ q z, z ∈ Metric.ball 0 r →
        ‖physicalChargeSummand D slot colour upperA c x q z‖ ≤ b q := by
  classical
  let Q := markedQuadratic D slot colour upperA c x
  let L := markedLinear D slot colour upperA c x
  obtain ⟨hQ, hL⟩ := marked_source_analytic D slot colour upperA c hx hx₁
  obtain ⟨b, hb, hbound⟩ := charge_exponential_majorant D hD
    (chartTau upperA c x) hτ Q L hQ.continuousAt (fun j => (hL j).continuousAt)
  have he : ∀ᶠ z in 𝓝 (0 : (X ⊕ X) → ℂ),
      (AnalyticAt ℂ Q z ∧ (∀ j, AnalyticAt ℂ (L j) z)) ∧
      ∀ q : Charge D, ‖physicalChargeSummand D slot colour upperA c x q z‖ ≤ b q := by
    filter_upwards [hQ.eventually_analyticAt,
      eventually_all.mpr (fun j => (hL j).eventually_analyticAt), hbound] with z hz hsz hB
    refine ⟨⟨hz, hsz⟩, fun q => ?_⟩
    simpa only [physicalChargeSummand, markedLinear_eq] using hB q
  obtain ⟨r, hr, hballs⟩ := Metric.eventually_nhds_iff.mp he
  have hF (q : Charge D) :
      AnalyticOnNhd ℂ (physicalChargeSummand D slot colour upperA c x q)
        (Metric.ball 0 r) := by
    intro z hz
    obtain ⟨hzQ, hzL⟩ := (hballs hz).1
    unfold physicalChargeSummand
    simp_rw [markedLinear_eq]
    refine analyticAt_const.mul ((hzQ.add ?_).cexp)
    exact Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul (hzL j)
  exact ⟨b, r, hb, hr, hF, fun q z hz => (hballs hz).2 q⟩

variable [DecidableEq X]

/-- At a fixed point of the real overlap, the simultaneous spatial and
marking Taylor coefficient of the physical sector is the convergent sum
of the same coefficient of its literal charge summands. -/
theorem physical_chart_jet_hasSum (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (slot : X → Puncture) (colour : X → Fin D.rank)
    (upperA : Bool) (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (hp : chartPeriod upperA c x ≠ 0) (hτ : 0 < (chartTau upperA c x).im)
    (a : ModTwoCharge D) (n : X ⊕ X → ℕ) (l : List (X ⊕ X)) :
    HasSum (fun q : {q : Charge D // reduceCharge D q = a} =>
      (chartPeriod upperA c x ^ (12 : ℕ))⁻¹ *
        spatialCoefficient n l (physicalChargeSummand D slot colour upperA c x q.val) 0)
      (spatialCoefficient n l (fun z => physicalProduct D hu slot colour upperA x c a
        (z ∘ Sum.inl) (z ∘ Sum.inr)) 0) := by
  classical
  obtain ⟨b, r, hb, hr, hF, hbound⟩ :=
    physical_charge_summands_normal D hD slot colour upperA c hx hx₁ hτ
  have hs := spatialCoefficient_hasSum (hb.subtype (fun q => reduceCharge D q = a)) hr
    (fun q => hF q.val) (fun q z hz => hbound q.val z hz) n l
  have heq : (fun z => physicalProduct D hu slot colour upperA x c a
      (z ∘ Sum.inl) (z ∘ Sum.inr)) = fun z => (chartPeriod upperA c x ^ (12 : ℕ))⁻¹ *
        ∑' q : {q : Charge D // reduceCharge D q = a},
          physicalChargeSummand D slot colour upperA c x q.val z := by
    funext z
    exact physical_product_marked_charge_fiber D hu slot colour upperA c x hp a _ _
  rw [heq, spatialCoefficient_const_mul]
  exact hs.mul_left _

open OriginalFourMChargeCoset (fourierSign quadraticSign)
open OriginalFourMPhysicalProduct (physical_chart_product)

private theorem tsum_charge_fibres (D : LatticeData) (f : Charge D → ℂ)
    (hf : Summable f) (k : ModTwoCharge D → ℂ) :
    (∑' q : Charge D, k (reduceCharge D q) * f q) =
      ∑ a : ModTwoCharge D, k a * ∑' q : {q : Charge D // reduceCharge D q = a}, f q.val := by
  classical
  let C : ℝ := ∑ a : ModTwoCharge D, ‖k a‖
  have hC (a : ModTwoCharge D) : ‖k a‖ ≤ C :=
    Finset.single_le_sum (fun i _ => norm_nonneg (k i)) (Finset.mem_univ a)
  have hs : Summable (fun q : Charge D => k (reduceCharge D q) * f q) := by
    apply (hf.norm.mul_left C).of_norm_bounded
    intro q
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  have h := (hs.hasSum.tsum_fiberwise (reduceCharge D)).tsum_eq
  rw [tsum_fintype] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro a _
  rw [← tsum_mul_left]
  apply tsum_congr
  intro q
  have hq : reduceCharge D q.val = a := q.property
  rw [hq]

private theorem weighted_physical_chart_jet (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (slot : X → Puncture) (colour : X → Fin D.rank)
    (upperA : Bool) (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (k : ModTwoCharge D → ℂ) (n : X ⊕ X → ℕ) (l : List (X ⊕ X)) :
    let F := fun a (z : (X ⊕ X) → ℂ) => physicalProduct D hu slot colour upperA x c a
      (z ∘ Sum.inl) (z ∘ Sum.inr)
    spatialCoefficient n l (fun z => ∑ a, k a * F a z) 0 =
      ∑ a, k a * spatialCoefficient n l (F a) 0 := by
  classical
  dsimp only
  obtain ⟨hp, hτ⟩ := chart_charge_data upperA c hx hx₁
  let F := physicalChargeSummand D slot colour upperA c x
  obtain ⟨b, r, hb, hr, hF, hbound⟩ :=
    physical_charge_summands_normal D hD slot colour upperA c hx hx₁ hτ
  let C : ℝ := ∑ a : ModTwoCharge D, ‖k a‖
  have hk (a : ModTwoCharge D) : ‖k a‖ ≤ C :=
    Finset.single_le_sum (fun i _ => norm_nonneg (k i)) (Finset.mem_univ a)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => norm_nonneg (k i))
  have hB (q : Charge D) (z : (X ⊕ X) → ℂ) (hz : z ∈ Metric.ball 0 r) :
      ‖k (reduceCharge D q) * F q z‖ ≤ C * b q := by
    rw [norm_mul]
    exact mul_le_mul (hk _) (hbound q z hz) (norm_nonneg _) hC
  let G (q : Charge D) (z : (X ⊕ X) → ℂ) := k (reduceCharge D q) * F q z
  have hs := spatialCoefficient_hasSum (f := G) (hb.mul_left C) hr
    (fun q z hz => analyticAt_const.mul (hF q z hz)) hB n l
  have hs0 := spatialCoefficient_hasSum hb hr hF hbound n l
  let p := (chartPeriod upperA c x ^ (12 : ℕ))⁻¹
  have he : (fun z : (X ⊕ X) → ℂ => ∑ a, k a *
      physicalProduct D hu slot colour upperA x c a (z ∘ Sum.inl) (z ∘ Sum.inr)) =ᶠ[𝓝 0]
      (fun z => p * ∑' q : Charge D, k (reduceCharge D q) * F q z) := by
    filter_upwards [Metric.ball_mem_nhds (0 : (X ⊕ X) → ℂ) hr] with z hz
    rw [tsum_charge_fibres D (fun q => F q z) (hb.of_norm_bounded fun q => hbound q z hz),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [physical_product_marked_charge_fiber D hu slot colour upperA c x hp]
    change k a * (p * ∑' q : {q : Charge D // reduceCharge D q = a}, F q.val z) = _
    ring
  rw [(spatialCoefficient_congr n l he).eq_of_nhds, spatialCoefficient_const_mul]
  change p * spatialCoefficient n l (fun z => ∑' q, G q z) 0 = _
  rw [← hs.tsum_eq]
  have hjet (q : Charge D) : spatialCoefficient n l (G q) 0 =
      k (reduceCharge D q) * spatialCoefficient n l (F q) 0 :=
    congrFun (spatialCoefficient_const_mul n l _ _) 0
  simp_rw [hjet]
  rw [tsum_charge_fibres D _ hs0.summable, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← (physical_chart_jet_hasSum D hu hD slot colour upperA c hx hx₁ hp hτ a n l).tsum_eq,
    tsum_mul_left]
  change p * (k a * _) = k a * (p * _)
  ring


/-- The simultaneous Taylor coefficients of the actual physical products
inherit the real-overlap sector identities by normal convergence on a
common polydisk. -/
theorem physical_chart_coefficient_overlap (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (hr : D.rank = 24)
    (slot : X → Puncture) (colour : X → Fin D.rank) (upperA : Bool)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    {w : ℂ} (hwA : w ^ 2 = parameter .A x) (hw : ‖w‖ < 1)
    (n : X ⊕ X → ℕ) (l : List (X ⊕ X))
    (a : ModTwoCharge D) :
    let jet := fun c a => spatialCoefficient n l (fun z : (X ⊕ X) → ℂ =>
        physicalProduct D hu slot colour upperA x c a (z ∘ Sum.inl) (z ∘ Sum.inr)) 0
    jet .D a = ((2 : ℂ) ^ (12 : ℕ))⁻¹ * (∑ b, fourierSign D a b * jet .A b) ∧
    jet .B a = (periodRoot .A x ^ (12 : ℕ))⁻¹ *
      (((2 : ℂ) ^ (12 : ℕ))⁻¹ * ∑ b, fourierSign D a b * quadraticSign D b * jet .A b) := by
  classical
  dsimp only
  let F (c : Chart) (a : ModTwoCharge D) (z : (X ⊕ X) → ℂ) :=
    physicalProduct D hu slot colour upperA x c a (z ∘ Sum.inl) (z ∘ Sum.inr)
  let T := fun f => spatialCoefficient n l f 0
  change T (F .D a) = _ ∧ T (F .B a) = _
  let L := Pi.compRightL ℂ (fun _ : X ⊕ X => ℂ) (Sum.inl : X → X ⊕ X)
  have he := physical_chart_product D hu hD hr slot colour upperA hx hx₁ hwA hw
  have hL : Tendsto L (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (L.continuous.continuousAt (x := 0)).tendsto
  have h := hL.eventually he
  have hD' : F .D a =ᶠ[𝓝 0] (fun z => ((2 : ℂ) ^ (12 : ℕ))⁻¹ *
      ∑ b, fourierSign D a b * F .A b z) := by
    filter_upwards [h] with u hu
    exact (hu (u ∘ Sum.inr) a).1
  have hB' : F .B a =ᶠ[𝓝 0] (fun z => (periodRoot .A x ^ (12 : ℕ))⁻¹ *
      (((2 : ℂ) ^ (12 : ℕ))⁻¹ * ∑ b, fourierSign D a b * quadraticSign D b * F .A b z)) := by
    filter_upwards [h] with u hu
    exact (hu (u ∘ Sum.inr) a).2
  have hsum (k : ModTwoCharge D → ℂ) :
      T (fun z => ∑ b, k b * F .A b z) = ∑ b, k b * T (F .A b) :=
    weighted_physical_chart_jet D hu hD slot colour upperA .A hx hx₁ k n l
  constructor
  · rw [show T (F .D a) = _ from (spatialCoefficient_congr n l hD').eq_of_nhds]
    rw [spatialCoefficient_const_mul]
    simpa only [T, F] using congrArg (fun t : ℂ => ((2 : ℂ) ^ (12 : ℕ))⁻¹ * t)
      (hsum (fourierSign D a))
  · rw [show T (F .B a) = _ from (spatialCoefficient_congr n l hB').eq_of_nhds]
    rw [spatialCoefficient_const_mul, spatialCoefficient_const_mul]
    simpa only [T, F] using congrArg (fun t : ℂ => (periodRoot .A x ^ (12 : ℕ))⁻¹ *
      (((2 : ℂ) ^ (12 : ℕ))⁻¹ * t)) (hsum (fun b => fourierSign D a b * quadraticSign D b))


open NativeAffineExternalCoefficient (coordinateJet jetOccupation)
open NativeAffineTransport (affineExponent)
open OriginalChargedRowSource (affineMoment affineMoment_coefficient)
open OriginalFourMPhysicalCovariance (physical_covariance_swap)

private theorem mark_jet_eq_moment (D : LatticeData) (slot : X → Puncture)
    (colour : X → Fin D.rank) (upperA : Bool) (c : Chart) (x : ℝ)
    (q : Charge D) (l : List X) (u : X → ℂ) :
    let A : Matrix X X ℂ := fun i j =>
      physicalEntry D upperA c x slot colour i j (u i) (u j) *
        relative c (slot i) * relative c (slot j)
    let m := fun i => physicalMean D q upperA c x slot colour i (u i) * relative c (slot i)
    coordinateJet l (fun v => physicalChargeSummand D slot colour upperA c x q (Sum.elim u v)) 0 =
      Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x * (bilinear D q q : ℂ) / 2) *
        affineMoment A m (jetOccupation l) := by
  classical
  dsimp only
  let A : Matrix X X ℂ := fun i j =>
    physicalEntry D upperA c x slot colour i j (u i) (u j) *
      relative c (slot i) * relative c (slot j)
  let m := fun i => physicalMean D q upperA c x slot colour i (u i) * relative c (slot i)
  have hs (i j : X) : A i j = A j i := by
    change (D.G (colour i) (colour j) : ℂ) *
        physicalCovariance upperA c x (slot i) (slot j) (u i) (u j) *
          relative c (slot i) * relative c (slot j) = _
    rw [physical_covariance_swap upperA c x (slot i) (slot j) (u i) (u j)]
    simp only [A, physicalEntry, D.symmetric (colour j) (colour i)]
    ring
  let p := Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x *
    (bilinear D q q : ℂ) / 2)
  have he (v : X → ℂ) : physicalChargeSummand D slot colour upperA c x q (Sum.elim u v) =
      p * Complex.exp (MvPolynomial.eval v (affineExponent A m)) := by
    unfold physicalChargeSummand
    congr 2
    simp only [markedQuadratic, affineExponent, FactorialFockQuadraticEstimate.quadratic,
      map_add, map_sum, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [A]
      ring
    · apply Finset.sum_congr rfl
      intro i _
      dsimp only [m]
      ring
  simp_rw [he, NativeAffineExternalCoefficient.coordinateJet_const_mul]
  congr 1
  have h := NativeAffineExternalCoefficient.native_affine_external_jet A m hs l _ le_rfl
  change _ = affineMoment A m (jetOccupation l)
  rw [affineMoment_coefficient]
  have hweight : (FactorialFockMetric.weight (jetOccupation l) : ℂ) ≠ 0 := by
    exact_mod_cast (FactorialFockMetric.weight_pos (jetOccupation l)).ne'
  exact ((div_eq_iff hweight).1 h).trans (mul_comm _ _)

/-- Selecting the distinct marks once in the physical product gives a
normally convergent sum of their charge-dependent native Wick moments.
The spatial Taylor coefficients are taken after the mark extraction. -/
theorem physical_chart_marked_coefficient_hasSum (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (slot : X → Puncture) (colour : X → Fin D.rank)
    (upperA : Bool) (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (a : ModTwoCharge D) (n : X → ℕ) (l : List X) (hl : l.Nodup) :
    let A : (X → ℂ) → Matrix X X ℂ := fun u i j =>
      (D.G (colour i) (colour j) : ℂ) *
        physicalCovariance upperA c x (slot i) (slot j) (u i) (u j) *
          relative c (slot i) * relative c (slot j)
    let m := fun (q : Charge D) (u : X → ℂ) i =>
      -(bilinear D (unitCharge D (colour i)) q : ℂ) *
        physicalSource c x (slot i) (u i) / chartPeriod upperA c x * relative c (slot i)
    HasSum (fun q : {q : Charge D // reduceCharge D q = a} =>
      (chartPeriod upperA c x ^ (12 : ℕ))⁻¹ *
        Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x *
          (bilinear D q.val q.val : ℂ) / 2) *
          spatialCoefficient n l (fun u => affineMoment (A u) (m q.val u) (jetOccupation l)) 0)
      (spatialCoefficient (Sum.elim n (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl)
        (fun z => physicalProduct D hu slot colour upperA x c a
          (z ∘ Sum.inl) (z ∘ Sum.inr)) 0) := by
  classical
  dsimp only
  obtain ⟨hp, hτ⟩ := chart_charge_data upperA c hx hx₁
  have hs := physical_chart_jet_hasSum D hu hD slot colour upperA c hx hx₁ hp hτ a
    (Sum.elim n (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl)
  have he (q : Charge D) := spatialCoefficient_split_marks n l hl
    (physicalChargeSummand D slot colour upperA c x q)
  simp_rw [he, mark_jet_eq_moment D slot colour upperA c x,
    spatialCoefficient_const_mul, ← mul_assoc] at hs
  exact hs

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWick
