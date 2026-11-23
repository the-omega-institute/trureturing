/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickPartition
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickPartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Spatially extracted native and correction factors of the physical marked jet. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccurrenceWick
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickExtraction

/-! Evaluate the correction and native factors independently at the
requested spatial modes of the physical occurrence word. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWickPartition

open LatticeGeneratingFieldLocality LatticeHalfFock
open FourPoint.OriginalFourMActualChart
open OriginalFourMOccupationTransport (flags rawLocal inverseRoot inverseRoot_analytic
  inverseRoot_zero root_ne halfJacobian physicalSource_analytic)
open OriginalFourMPhysicalCovariance (jac slotCorrection relative physicalCovariance
  physicalCovariance_analytic)
open OriginalFourMPhysicalProduct (physicalChargeSummand physicalEntry physicalMean)
open OriginalFourMSignedOverlap (chartCovariance)
open OriginalFourMChartProduct (chartTau)
open OriginalFourMSpatialWick (spatialCoefficient)
open OriginalFourMOccurrenceWick (correctionEntry nativeEntry liftedScale
  physical_marked_coefficient_partition correction_pair_coefficient)
open OriginalFourMSpatialWickExtraction (wick_analytic wick_dependsOn DependsOn
  partition_eq_filters spatialCoefficient_list_sum spatialCoefficient_mul_partition
  spatialCoefficient_wick)
open OriginalGaussianSewnAnalytic (coefficient)
open HalfFock.OriginalHalfCurrentWickPolynomial (pair)
open AffineOccurrenceWick (wick)
open AffineWickConvolution (partitions)
open private same_flags freeCorrection comp_fst comp_snd from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance

variable {X : Type*}

private def correctionKernel (D : LatticeData) (c : Chart) (x : ℝ) (slot : X → Puncture)
    (colour : X → Fin D.rank) (i j : X) (u v : ℂ) : ℂ :=
  (D.G (colour i) (colour j) : ℂ) *
    (-(slotCorrection c x (slot i) (slot j) u v) /
      (jac c x (slot i) u * jac c x (slot j) v)) *
    relative c (slot i) * relative c (slot j)

private def nativeKernel (D : LatticeData) (upperA : Bool) (c : Chart) (x : ℝ)
    (slot : X → Puncture) (colour : X → Fin D.rank) (i j : X) (u v : ℂ) : ℂ :=
  (D.G (colour i) (colour j) : ℂ) *
    (chartCovariance upperA c x (flags c (slot i)).1 (flags c (slot j)).1
      (flags c (slot i)).2 (flags c (slot j)).2
      (rawLocal c x (slot i) u) (rawLocal c x (slot j) v) /
      (jac c x (slot i) u * jac c x (slot j) v)) *
    relative c (slot i) * relative c (slot j)

private theorem correctionKernel_analytic (D : LatticeData) (c : Chart) {x : ℝ}
    (hx : 0 < x) (hx₁ : x < 1) (slot : X → Puncture) (colour : X → Fin D.rank) (a b : X) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => correctionKernel D c x slot colour a b z.1 z.2) (0, 0) := by
  have hJ (s : Puncture) : AnalyticAt ℂ (jac c x s) 0 :=
    analyticAt_const.div ((inverseRoot_analytic hx hx₁ c s).pow 3) (by simp [inverseRoot_zero])
  have hS : AnalyticAt ℂ (fun z : ℂ × ℂ =>
      slotCorrection c x (slot a) (slot b) z.1 z.2) (0, 0) := by
    unfold slotCorrection
    split
    · unfold freeCorrection
      have h₁ := comp_fst (inverseRoot_analytic hx hx₁ c (slot a))
      have h₂ := comp_snd (inverseRoot_analytic hx hx₁ c (slot a))
      exact (analyticAt_const.mul (analyticAt_const.add (h₁.mul h₂))).div
        (((analyticAt_const.mul h₁).mul h₂).mul ((h₁.add h₂).pow 2))
        (by norm_num [inverseRoot_zero])
    · exact analyticAt_const
  exact ((analyticAt_const.mul (hS.neg.div
    ((comp_fst (hJ (slot a))).mul (comp_snd (hJ (slot b))))
    (by simp [jac, halfJacobian, inverseRoot_zero, root_ne hx hx₁]))).mul
    analyticAt_const).mul analyticAt_const

private theorem nativeKernel_analytic (D : LatticeData) (upperA : Bool) (c : Chart) {x : ℝ}
    (hx : 0 < x) (hx₁ : x < 1) (slot : X → Puncture) (colour : X → Fin D.rank) (a b : X) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => nativeKernel D upperA c x slot colour a b z.1 z.2) (0, 0) := by
  have hP : AnalyticAt ℂ (fun z : ℂ × ℂ =>
      physicalEntry D upperA c x slot colour a b z.1 z.2 *
        relative c (slot a) * relative c (slot b)) (0, 0) :=
    ((analyticAt_const.mul (physicalCovariance_analytic upperA hx hx₁ c (slot a) (slot b))).mul
      analyticAt_const).mul analyticAt_const
  have h := hP.sub (correctionKernel_analytic D c hx hx₁ slot colour a b)
  convert h using 1
  funext z
  simp only [physicalEntry, physicalCovariance, correctionKernel, nativeKernel, sub_div, neg_div,
    Pi.sub_apply]
  ring

/-- The Taylor-indexed native chart covariance retains both endpoint degrees. -/
def nativeTaylor (D : LatticeData) (upperA : Bool) (c : Chart) (x : ℝ)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) : Matrix X X ℂ :=
  Matrix.of fun i j => coefficient (n j) (fun v =>
    coefficient (n i) fun u => nativeKernel D upperA c x slot colour i j u v)

/-- The Taylor-indexed correction is the scaled central contraction, supported
only within one physical puncture. -/
def correctionTaylor (D : LatticeData) (c : Chart) (x : ℝ) (slot : X → Puncture)
    (colour : X → Fin D.rank) (n : X → ℕ) : Matrix X X ℂ :=
  open Classical in
  Matrix.of fun i j => if slot i = slot j then
    liftedScale c x (slot i) (n i) * liftedScale c x (slot j) (n j) *
      MvPolynomial.constantCoeff ((pair D (colour i, n i) (colour j, n j)).eval
        (MvPolynomial.C (-loweringParameter c (slot i))))
    else 0

private theorem correctionKernel_coeff (D : LatticeData) (c : Chart) {x : ℝ}
    (hx : 0 < x) (hx₁ : x < 1) (slot : X → Puncture) (colour : X → Fin D.rank)
    (n : X → ℕ) (i j : X) :
    coefficient (n j) (fun v => coefficient (n i) fun u =>
      correctionKernel D c x slot colour i j u v) = correctionTaylor D c x slot colour n i j := by
  classical
  by_cases h : slot i = slot j
  · simp only [correctionTaylor, Matrix.of_apply, h, ite_true, correctionKernel]
    convert correction_pair_coefficient D hx hx₁ c (slot j)
      (colour i, n i) (colour j, n j) using 1
    congr 1
    funext v
    congr 1
    funext u
    simp only [neg_div]
    ring
  · have hn : ¬ ((flags c (slot i)).1 = (flags c (slot j)).1 ∧
        (flags c (slot i)).2 = (flags c (slot j)).2) := fun hf => h (same_flags c hf)
    simp [correctionKernel, correctionTaylor, slotCorrection, coefficient, h, ite_eq_right hn]

variable [Fintype X] [DecidableEq X]

private theorem pair_projection_analytic {f : ℂ × ℂ → ℂ}
    (hf : AnalyticAt ℂ f (0, 0)) (i j : X) :
    AnalyticAt ℂ (fun u : X → ℂ => f (u i, u j)) 0 := by
  have hp (k : X) : AnalyticAt ℂ (fun u : X → ℂ => u k) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : X => ℂ) k).analyticAt 0
  apply hf.comp_of_eq (f := fun u : X → ℂ => (u i, u j)) ((hp i).prod (hp j))
  rfl

set_option maxHeartbeats 500000 in
/-- The physical fixed-charge marked coefficient equals the finite sum of
spatially extracted Wick factors grouped by the correction endpoint set.
The correction branch is the actual central polynomial with both lifted scales. -/
theorem physical_marked_coefficient_wick_partition (D : LatticeData)
    (slot : X → Puncture) (colour : X → Fin D.rank) (upperA : Bool) (c : Chart) {x : ℝ}
    (hx : 0 < x) (hx₁ : x < 1) (q : Charge D) (n : X → ℕ) (l : List X) (hl : l.Nodup) :
    spatialCoefficient (Sum.elim n (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl)
      (physicalChargeSummand D slot colour upperA c x q) 0 =
      Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x * (bilinear D q q : ℂ) / 2) *
        ((partitions l).map fun p => wick (correctionTaylor D c x slot colour n) 0 p.1 *
          wick (nativeTaylor D upperA c x slot colour n)
            (fun i => coefficient (n i) (fun u =>
              physicalMean D q upperA c x slot colour i u * relative c (slot i))) p.2).sum := by
  rw [physical_marked_coefficient_partition D slot colour upperA c x q n l hl]
  apply congrArg (fun t : ℂ => Complex.exp ((Real.pi : ℂ) * Complex.I *
    chartTau upperA c x * (bilinear D q q : ℂ) / 2) * t)
  let C := correctionKernel D c x slot colour
  let N := nativeKernel D upperA c x slot colour
  let μ := fun i u => physicalMean D q upperA c x slot colour i u * relative c (slot i)
  let WC := fun (s : List X) (u : X → ℂ) => wick (Matrix.of fun i j => C i j (u i) (u j)) (fun _ => 0) s
  let WN := fun (s : List X) (u : X → ℂ) => wick (Matrix.of fun i j => N i j (u i) (u j)) (fun i => μ i (u i)) s
  let AC (u : X → ℂ) : Matrix X X ℂ := Matrix.of fun i j => C i j (u i) (u j)
  let AN (u : X → ℂ) : Matrix X X ℂ := Matrix.of fun i j => N i j (u i) (u j)
  let M (u : X → ℂ) (i : X) := μ i (u i)
  have hp (i : X) : AnalyticAt ℂ (fun u : X → ℂ => u i) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : X => ℂ) i).analyticAt _
  have hc (i j : X) : AnalyticAt ℂ (fun u : X → ℂ => C i j (u i) (u j)) 0 :=
    pair_projection_analytic (f := fun z => C i j z.1 z.2)
      (correctionKernel_analytic D c hx hx₁ slot colour i j) i j
  have hn (i j : X) : AnalyticAt ℂ (fun u : X → ℂ => N i j (u i) (u j)) 0 :=
    pair_projection_analytic (f := fun z => N i j z.1 z.2)
      (nativeKernel_analytic D upperA c hx hx₁ slot colour i j) i j
  have hm (i : X) : AnalyticAt ℂ (fun u : X → ℂ => μ i (u i)) 0 := by
    have h : AnalyticAt ℂ (μ i) 0 := by
      unfold μ physicalMean
      exact ((analyticAt_const.mul (physicalSource_analytic hx hx₁ c (slot i))).div_const).mul
        analyticAt_const
    exact h.comp_of_eq (f := fun u : X → ℂ => u i) (hp i) rfl
  have hzero (i : X) : AnalyticAt ℂ (fun _ : X → ℂ => (0 : ℂ)) 0 :=
    analyticAt_const
  have hWC (s : List X) : AnalyticAt ℂ (WC s) 0 :=
    wick_analytic AC (fun _ _ => 0) hc hzero s
  have hWN (s : List X) : AnalyticAt ℂ (WN s) 0 := wick_analytic AN M hn hm s
  change spatialCoefficient n l (fun u => ((partitions l).map fun p =>
    WC p.1 u * WN p.2 u).sum) 0 = _
  rw [spatialCoefficient_list_sum n l (partitions l) (fun p u => WC p.1 u * WN p.2 u)
    (fun p _ => (hWC p.1).mul (hWN p.2))]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hmem
  have ⟨h₁, h₂⟩ := partition_eq_filters l p hl hmem
  have nd₁ : p.1.Nodup := h₁ ▸ hl.filter (fun a => decide (a ∈ p.1))
  have nd₂ : p.2.Nodup := h₂ ▸ hl.filter (fun a => !decide (a ∈ p.1))
  rw [spatialCoefficient_mul_partition n l hl p hmem (WC p.1) (WN p.2)
    (wick_dependsOn C (fun _ _ => 0) p.1) (wick_dependsOn N μ p.2)]
  have hCT : (Matrix.of fun i j => coefficient (n j) (fun v =>
    coefficient (n i) fun u => C i j u v)) = correctionTaylor D c x slot colour n := by
    ext i j
    exact correctionKernel_coeff D c hx hx₁ slot colour n i j
  have he (i : X) : coefficient (n i) (fun _ => 0) = 0 := by
    simp [coefficient]
  have he' : (fun i => coefficient (n i) (fun _ => 0)) = (0 : X → ℂ) := funext he
  have hcw := spatialCoefficient_wick C (fun _ _ => 0) hc hzero n p.1 nd₁
  rw [hCT, he'] at hcw
  have hnw := spatialCoefficient_wick N μ hn hm n p.2 nd₂
  exact congrArg₂ (· * ·) hcw hnw

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWickPartition
