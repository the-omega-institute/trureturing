/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipOccupation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipOccupation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite oscillator occupation readout at the original D boundary. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipTransport
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWick

/-! At the actual D boundary, the marked coefficient evaluates the four
inverse-lowered words in the finite Gaussian with the continued entries. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean

open LatticeGeneratingFieldLocality MvPolynomial
open OriginalFourMActualChart (Chart Puncture parameter)
open OriginalFourMOccupationTransport (flags physicalSource)
open OriginalFourMPhysicalCovariance (physicalCovariance)
open OriginalFourMJointWick (BoundedExternal marked_gaussian_slot_words)
open OriginalGaussianSewnAnalytic (coefficient)
open NativeAffineTransport (transportMean transportCovariance transportCovariance_symm)
open NativeAffineExternalCoefficient (coordinateJet jetOccupation)
open OriginalChargedRowSource (affineCoefficient affineMoment affineMoment_coefficient)
open OriginalFourMSpatialWick (spatialCoefficient spatial_marked_gaussian)
open FactorialFockMetric (weight)
open private dMatrix dLinear from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipSector
open private leg from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSectorContinuation
open private chartPeriod from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChartProduct
open private nativeLabel externalLabel creatorMatrix creator_matrix_sum gramCorrection
  gramCorrection_symm boundedWord bounded_word_step from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMJointWick
open private incomingScale wordScale from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCauchyTaylor
open OriginalFourMCauchyTaylor (inverseLoweredWord)
open private same_flags physicalCovariance_analytic from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance
open private physicalSource_analytic from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccupationTransport
open private physicalEntry physicalMean physical_covariance_swap from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWick
open private coefficient_mul_scalar from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCauchyTaylor
open private evalLower from D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentFiniteLowering
open private vacuumProjection_apply from D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport

variable {X : Type*} [Fintype X] [DecidableEq X]

private def boundaryMean (D : LatticeData) (q : Charge D) (N : ℕ) (z : ℝ)
    (i : BoundedExternal D N ⊕ BoundedExternal D N) : ℂ :=
  let label := Sum.elim (externalLabel D N) (externalLabel D N)
  (bilinear D (unitCharge D (label i).2.1) q : ℂ) *
    dLinear D true (externalLabel D N) (parameter .D (z : ℂ)) i

private theorem selected_dLip_mean_matrix (D : LatticeData) (q : Charge D) (N : ℕ)
    {z : ℝ} (hz : 0 < z) (hz₁ : z < 1) (slot : X → Puncture)
    (mode : X → Index D) (bound : ∀ i, (mode i).2 ≤ N) (i : X) :
    coefficient (mode i).2 (fun u =>
      -(bilinear D (unitCharge D (mode i).1) q : ℂ) *
        physicalSource .D z (slot i) u / chartPeriod true .D z) =
      transportMean (creatorMatrix D N .D z slot mode bound) (boundaryMean D q N z) i := by
  rw [selected_dLip_physical_mean D q hz hz₁, transportMean, creator_matrix_sum,
    Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [dite_eq_left (Finset.mem_range.mp hk)]
  congr 1
  unfold nativeLabel
  generalize (flags Chart.D (slot i)).1 = l
  cases l <;> rfl

private theorem selected_dLip_covariance_matrix (D : LatticeData) (hu : IsUnit D.G.det)
    (N : ℕ) {z : ℝ} (hz : 0 < z) (hz₁ : z < 1) (slot : X → Puncture)
    (mode : X → Index D) (bound : ∀ i, (mode i).2 ≤ N) (i j : X) :
    (D.G (mode i).1 (mode j).1 : ℂ) * coefficient (mode j).2
      (fun v => coefficient (mode i).2 (fun u =>
        physicalCovariance true .D z (slot i) (slot j) u v)) =
      (transportCovariance (creatorMatrix D N .D z slot mode bound)
        (dMatrix D true (externalLabel D N) (parameter .D (z : ℂ))) +
        gramCorrection D .D z slot mode) i j := by
  classical
  rw [selected_dLip_physical_covariance D hu hz hz₁]
  simp only [Matrix.add_apply]
  congr 1
  · let U := creatorMatrix D N .D z slot mode bound
    let A := dMatrix D true (externalLabel D N) (parameter .D (z : ℂ))
    have ht : transportCovariance U A i j = ∑ a, U i a * (∑ b, U j b * A a b) := by
      unfold transportCovariance
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    rw [ht]
    simp_rw [U, creator_matrix_sum]
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    rw [dite_eq_left (Finset.mem_range.mp hk), Finset.mul_sum, Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro l hl
    rw [dite_eq_left (Finset.mem_range.mp hl)]
    have hA :
        A (nativeLabel D N .D (slot i) (mode i).1
          ⟨k, lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.succ_le_succ (bound i))⟩)
          (nativeLabel D N .D (slot j) (mode j).1
          ⟨l, lt_of_lt_of_le (Finset.mem_range.mp hl) (Nat.succ_le_succ (bound j))⟩) =
        dLipCovarianceEntry D true (flags .D (slot i)).1 (flags .D (slot j)).1
          ((flags .D (slot i)).2, (mode i).1, k) ((flags .D (slot j)).2, (mode j).1, l)
          (parameter .D (z : ℂ)) := by
      dsimp only [A, nativeLabel]
      generalize (flags Chart.D (slot i)).1 = a
      generalize (flags Chart.D (slot j)).1 = b
      cases a <;> cases b <;> rfl
    rw [hA]
    ring
  · have he : ((flags .D (slot i)).1 = (flags .D (slot j)).1 ∧
        (flags .D (slot i)).2 = (flags .D (slot j)).2) ↔ slot i = slot j :=
      ⟨same_flags .D, fun h => by simp [h]⟩
    simp only [he, gramCorrection, incomingScale]

private theorem bounded_boundary_matrix_symm (D : LatticeData) (N : ℕ)
    {z : ℝ} (hz : 0 < z) (hz₁ : z < 1) (i j : BoundedExternal D N ⊕ BoundedExternal D N) :
    dMatrix D true (externalLabel D N) (parameter .D (z : ℂ)) i j =
      dMatrix D true (externalLabel D N) (parameter .D (z : ℂ)) j i := by
  unfold dMatrix
  dsimp only
  rw [parameter, ← Complex.ofReal_inv]
  exact dLip_covariance_entry_swap D true _ _ _ _ ((one_lt_inv₀ hz).2 hz₁)

/-- The simultaneous marked physical D coefficient is the finite
factorial readout of the original inverse-lowered words at its boundary. -/
theorem dLip_marked_occupation (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (N : ℕ) {z : ℝ} (hz : 0 < z) (hz₁ : z < 1)
    (slot : X → Puncture) (mode : X → Index D) (bound : ∀ i, (mode i).2 ≤ N)
    (ls : List (Puncture × List X)) (hslots : (ls.map Prod.fst).Nodup)
    (hv : ∀ entry ∈ ls, ∀ j ∈ entry.2, slot j = entry.1) :
    let B := fun i j => (D.G (mode i).1 (mode j).1 : ℂ) * coefficient (mode j).2
      (fun v => coefficient (mode i).2 (fun u =>
        physicalCovariance true .D z (slot i) (slot j) u v))
    let m := fun i => coefficient (mode i).2 (fun u =>
      -(bilinear D (unitCharge D (mode i).1) q : ℂ) *
        physicalSource .D z (slot i) u / chartPeriod true .D z)
    let P := (ls.map (fun entry => boundedWord D N .D z entry.1 (entry.2.map mode))).prod
    let A := dMatrix D true (externalLabel D N) (parameter .D (z : ℂ))
    let mu := boundaryMean D q N z
    coordinateJet (ls.flatMap Prod.snd) (fun v => Complex.exp (
      (1 / 2 : ℂ) * (∑ i, ∑ j, B i j * v i * v j) + ∑ i, m i * v i)) 0 =
      ∑ e ∈ P.support, P.coeff e * ((weight e : ℂ) * affineCoefficient A mu e) := by
  classical
  dsimp only
  simp_rw [selected_dLip_covariance_matrix D hu N hz hz₁ slot mode bound,
    selected_dLip_mean_matrix D q N hz hz₁ slot mode bound]
  apply marked_gaussian_slot_words slot (creatorMatrix D N .D z slot mode bound)
    (dMatrix D true (externalLabel D N) (parameter .D (z : ℂ)))
    (gramCorrection D .D z slot mode) (boundaryMean D q N z)
    (bounded_boundary_matrix_symm D N hz hz₁)
    (gramCorrection_symm D hu .D z slot mode) _
    (fun s l => boundedWord D N .D z s (l.map mode)) _
    (bounded_word_step D N .D z slot mode bound) ls hslots hv
  · intro i j hij
    simp [gramCorrection, hij]
  · intro s
    simp [boundedWord, inverseLoweredWord, wordScale, evalLower,
      HalfFock.OriginalHalfCurrentFiniteLowering.wordPolynomial, vacuumProjection_apply]

/-- Spatial differentiation of the marked D Gaussian gives its actual
occupation readout, with each repeated mode carried by its own mark. -/
theorem dLip_spatial_occupation (D : LatticeData) (hu : IsUnit D.G.det)
    (q : Charge D) (N : ℕ) {z : ℝ} (hz : 0 < z) (hz₁ : z < 1)
    (slot : X → Puncture) (mode : X → Index D) (bound : ∀ i, (mode i).2 ≤ N)
    (ls : List (Puncture × List X)) (hslots : (ls.map Prod.fst).Nodup)
    (hv : ∀ entry ∈ ls, ∀ j ∈ entry.2, slot j = entry.1)
    (hl : (ls.flatMap Prod.snd).Nodup) :
    let l := ls.flatMap Prod.snd
    let K := physicalEntry D true .D z slot (fun i => (mode i).1)
    let m := physicalMean D q true .D z slot (fun i => (mode i).1)
    let P := (ls.map (fun entry => boundedWord D N .D z entry.1 (entry.2.map mode))).prod
    let A := dMatrix D true (externalLabel D N) (parameter .D (z : ℂ))
    let mu := boundaryMean D q N z
    spatialCoefficient (fun i => (mode i).2) l (fun u => coordinateJet l (fun v => Complex.exp (
      (1 / 2 : ℂ) * (∑ i, ∑ j, K i j (u i) (u j) * v i * v j) +
        ∑ i, m i (u i) * v i)) 0) 0 =
      ∑ e ∈ P.support, P.coeff e * ((weight e : ℂ) * affineCoefficient A mu e) := by
  classical
  dsimp only
  let K := physicalEntry D true .D z slot (fun i => (mode i).1)
  let m := physicalMean D q true .D z slot (fun i => (mode i).1)
  let n := fun i => (mode i).2
  let l := ls.flatMap Prod.snd
  have hK (i j : X) : AnalyticAt ℂ (fun uv : ℂ × ℂ => K i j uv.1 uv.2) (0, 0) :=
    analyticAt_const.mul (physicalCovariance_analytic true hz hz₁ .D (slot i) (slot j))
  have hm (i : X) : AnalyticAt ℂ (m i) 0 :=
    (analyticAt_const.mul (physicalSource_analytic hz hz₁ .D (slot i))).div_const
  have hs (u : X → ℂ) (i j : X) : K i j (u i) (u j) = K j i (u j) (u i) := by
    simp only [K, physicalEntry]
    rw [D.symmetric, physical_covariance_swap]
  have hscalar (i j : X) :
      (coefficient (n j) fun v => coefficient (n i) fun u => K i j u v) =
      (D.G (mode i).1 (mode j).1 : ℂ) * coefficient (mode j).2
        (fun v => coefficient (mode i).2 (fun u =>
          physicalCovariance true .D z (slot i) (slot j) u v)) := by
    simp only [K, physicalEntry, n, coefficient_mul_scalar]
  have hcoeff (i j : X) :
      (coefficient (n j) fun v => coefficient (n i) fun u => K i j u v) =
        (transportCovariance (creatorMatrix D N .D z slot mode bound)
          (dMatrix D true (externalLabel D N) (parameter .D (z : ℂ))) +
          gramCorrection D .D z slot mode) i j :=
    (hscalar i j).trans (selected_dLip_covariance_matrix D hu N hz hz₁ slot mode bound i j)
  have hsym (i j : X) :
      (coefficient (n j) fun v => coefficient (n i) fun u => K i j u v) =
      (coefficient (n i) fun u => coefficient (n j) fun v => K j i v u) := by
    rw [hcoeff, hcoeff, Matrix.add_apply, Matrix.add_apply,
      transportCovariance_symm _ _ (bounded_boundary_matrix_symm D N hz hz₁) i j,
      gramCorrection_symm D hu .D z slot mode i j]
  rw [spatial_marked_gaussian K m hs hK hm n hsym l hl]
  have h := dLip_marked_occupation D hu q N hz hz₁ slot mode bound ls hslots hv
  dsimp only at h
  let B : Matrix X X ℂ := fun i j => (D.G (mode i).1 (mode j).1 : ℂ) * coefficient (n j)
    (fun v => coefficient (mode i).2 (fun u => physicalCovariance true .D z (slot i) (slot j) u v))
  have hB (i j : X) : B i j = B j i :=
    (hscalar i j).symm.trans ((hsym i j).trans (hscalar j i))
  have hj := OriginalFourMPhysicalCovariance.marked_gaussian_jet (id : X → X) l B
    (fun i => coefficient (n i) (m i)) hB
  simp only [id_eq, List.map_id, B, n, m, physicalMean, l] at hj
  erw [hj] at h
  let A : Matrix X X ℂ := fun i j => coefficient (n j) fun v => coefficient (n i) fun u => K i j u v
  change affineMoment A (fun i => coefficient (n i) (m i)) (jetOccupation l) = _
  have hAB : A = B := funext fun i => funext (hscalar i)
  rw [hAB]
  exact (affineMoment_coefficient B _ (jetOccupation l)).trans h

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean
